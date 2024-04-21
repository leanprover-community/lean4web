
import { EditorApi, InfoviewApi, RpcConnected } from '@leanprover/infoview-api'

import { EventEmitter, Disposable } from 'vscode'
import * as ls from 'vscode-languageserver-protocol'
import { createConverter } from 'vscode-languageclient/lib/common/codeConverter'
import { toSocket, WebSocketMessageWriter, WebSocketMessageReader } from 'vscode-ws-jsonrpc'

import * as monaco from 'monaco-editor/esm/vs/editor/editor.api.js'
import { MonacoLanguageClient, LanguageClientOptions, IConnectionProvider } from 'monaco-languageclient'

const c2pConverter = createConverter(undefined)

const diagnosticsEmitter = new EventEmitter()
const restartedEmitter = new EventEmitter()

const project = 'MathlibLatest'

const clientOptions: LanguageClientOptions = {
  documentSelector: ['lean4'],
  middleware: {
    handleDiagnostics: (uri, diagnostics, next) => {
      next(uri, diagnostics)

      const diagnostics_ = diagnostics.map(d => c2pConverter.asDiagnostic(d))
      diagnosticsEmitter.fire({ uri: c2pConverter.asUri(uri), diagnostics: diagnostics_ })
    },
  }
}

const socketUrl = 'ws://' + window.location.host + '/websocket' + '/' + project
const connectionProvider : IConnectionProvider = {
  get: async () => {
    return await new Promise((resolve) => {
      const websocket = new WebSocket(socketUrl)
      websocket.addEventListener('open', () => {
        const socket = toSocket(websocket)
        const reader = new WebSocketMessageReader(socket)
        const writer = new WebSocketMessageWriter(socket)
        resolve({ reader, writer })
      })
    })
  }
}

export class LeanClient implements Disposable {
  client: MonacoLanguageClient | undefined

  async start (): Promise<void> {

    this.client = new MonacoLanguageClient({ id: 'lean4', name: 'Lean 4', clientOptions, connectionProvider })
    await this.client.start()

    restartedEmitter.fire()
  }
}

export class InfoProvider implements Disposable {

  private infoviewApi: InfoviewApi
  private editor: monaco.editor.IStandaloneCodeEditor

  public readonly client: LeanClient
  public readonly editorApi: EditorApi = {
    createRpcSession: async (uri) => {
      const result: RpcConnected = await this.client.client.sendRequest('$/lean/rpc/connect', { uri })
      return result.sessionId
    },
    sendClientRequest: async (_uri: string, method: string, params: any): Promise<any> => {
      return await this.client.client.sendRequest(method, params)
    },
    subscribeServerNotifications: async (method) => {

      if (method === 'textDocument/publishDiagnostics') {
        diagnosticsEmitter.event((params) => this.infoviewApi.gotServerNotification(method, params))
      }
    },

    subscribeClientNotifications: async (_method) => {
      throw new Error('Function not implemented.')
    },
    insertText: async (_text, _kind, _tdpp) => {
      throw new Error('Function not implemented.')
    },
    unsubscribeServerNotifications: function (_method: string): Promise<void> {
      throw new Error('Function not implemented.')
    },
    unsubscribeClientNotifications: function (_method: string): Promise<void> {
      throw new Error('Function not implemented.')
    },
    copyToClipboard: function (_text: string): Promise<void> {
      throw new Error('Function not implemented.')
    },
    applyEdit: function (_te: ls.WorkspaceEdit): Promise<void> {
      throw new Error('Function not implemented.')
    },
    showDocument: function (_show: ls.ShowDocumentParams): Promise<void> {
      throw new Error('Function not implemented.')
    },
    closeRpcSession: function (_sessionId: string): Promise<void> {
      throw new Error('Function not implemented.')
    },
    sendClientNotification: function (_uri: string, _method: string, _params: any): Promise<void> {
      throw new Error('Function not implemented.')
    }
  }

  constructor (client: LeanClient, editor: monaco.editor.IStandaloneCodeEditor) {

    this.client = client
    this.editor = editor

    restartedEmitter.event(() => this.initInfoView())
  }

  async setInfoviewApi (infoviewApi: InfoviewApi) {
    this.infoviewApi = infoviewApi
  }

  async initInfoView () {
    
    const uri = this.editor.getModel().uri.toString()
    const range = { start: { line: 0, character: 0 }, end: { line: 0, character: 0 } }
    await this.infoviewApi.initialize({ uri, range })
    await this.infoviewApi.serverRestarted(this.client.client.initializeResult)
  }
}
