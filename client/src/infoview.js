
import { EventEmitter } from 'vscode'
import { createConverter } from 'vscode-languageclient/lib/common/codeConverter'
import { toSocket, WebSocketMessageWriter, WebSocketMessageReader } from 'vscode-ws-jsonrpc'

import { MonacoLanguageClient } from 'monaco-languageclient'

const diagnosticsEmitter = new EventEmitter()
const restartedEmitter = new EventEmitter()

const project = 'MathlibLatest'

const socketUrl = `ws://${window.location.host}/websocket/${project}`

const clientOptions = {
  documentSelector: ['lean4'],
  middleware: {
    handleDiagnostics: (uri, diagnostics, next) => {
      next(uri, diagnostics)

      diagnosticsEmitter.fire({ uri: createConverter().asUri(uri), diagnostics })
    },
  }
}

const connectionProvider = {
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

export class LeanClient {
  
  async start () {

    this.client = new MonacoLanguageClient({ id: 'lean4', name: 'Lean 4', clientOptions, connectionProvider })
    await this.client.start()

    restartedEmitter.fire()
  }
}

export class InfoProvider {

  editorApi = {
    createRpcSession: async (uri) => {
      const result = await this.client.client.sendRequest('$/lean/rpc/connect', { uri })
      return result.sessionId
    },
    sendClientRequest: async (_uri, method, params) => {
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
    unsubscribeServerNotifications: function (_method) {
      throw new Error('Function not implemented.')
    },
    unsubscribeClientNotifications: function (_method) {
      throw new Error('Function not implemented.')
    },
    copyToClipboard: function (_text) {
      throw new Error('Function not implemented.')
    },
    applyEdit: function (_te) {
      throw new Error('Function not implemented.')
    },
    showDocument: function (_show) {
      throw new Error('Function not implemented.')
    },
    closeRpcSession: function (_sessionId) {
      throw new Error('Function not implemented.')
    },
    sendClientNotification: function (_uri, _method, _params) {
      throw new Error('Function not implemented.')
    }
  }

  constructor (client, editor) {

    this.client = client
    this.editor = editor

    restartedEmitter.event(() => this.initInfoView())
  }

  async setInfoviewApi (infoviewApi) {
    this.infoviewApi = infoviewApi
  }

  async initInfoView () {
    
    const uri = this.editor.getModel().uri.toString()
    const range = { start: { line: 0, character: 0 }, end: { line: 0, character: 0 } }
    await this.infoviewApi.initialize({ uri, range })
    await this.infoviewApi.serverRestarted(this.client.client.initializeResult)
  }
}
