/* This file is based on `vscode-lean4/vscode-lean4/src/infoview.ts ` */

import { Disposable, Uri, window, workspace, Position } from 'vscode'
import * as ls from 'vscode-languageserver-protocol'

import { LeanClient } from './client'
import { fromLanguageServerPosition, p2cConverter, toLanguageServerRange } from './utils'

import { EditorApi, InfoviewApi, TextInsertKind, RpcConnectParams, RpcConnected, RpcKeepAliveParams, RpcErrorCode } from '@leanprover/infoview-api'

import * as monaco from 'monaco-editor/esm/vs/editor/editor.api.js'

const keepAlivePeriodMs = 10000

async function rpcConnect (client: LeanClient, uri: ls.DocumentUri): Promise<string> {
  const connParams: RpcConnectParams = { uri }
  const result: RpcConnected = await client.sendRequest('$/lean/rpc/connect', connParams)
  return result.sessionId
}

class RpcSessionAtPos implements Disposable {
  keepAliveInterval?: NodeJS.Timeout
  client: LeanClient

  constructor (client: LeanClient, public sessionId: string, public uri: ls.DocumentUri) {
    this.client = client
    this.keepAliveInterval = setInterval(async () => {
      const params: RpcKeepAliveParams = { uri, sessionId }
      try {
        await client.sendNotification('$/lean/rpc/keepAlive', params)
      } catch (e) {
        console.log(`[InfoProvider] failed to send keepalive for ${uri}: ${e}`)
        if (this.keepAliveInterval != null) clearInterval(this.keepAliveInterval)
      }
    }, keepAlivePeriodMs)
  }
}

export class InfoProvider implements Disposable {
  /** Instance of the panel, if it is open. Otherwise `undefined`. */
  private infoviewApi?: InfoviewApi
  private editor?: monaco.editor.IStandaloneCodeEditor
  private readonly subscriptions: Disposable[] = []
  private readonly clientSubscriptions: Disposable[] = []

  public readonly client?: LeanClient

  // Subscriptions are counted and only disposed of when count becomes 0.
  private readonly serverNotifSubscriptions: Map<string, [number, Disposable[]]> = new Map()

  private rpcSessions: Map<string, RpcSessionAtPos> = new Map()

  private subscribeDiagnosticsNotification (client: LeanClient, method: string) {
    const h = client.diagnostics((params) => {
      void this.infoviewApi?.gotServerNotification(method, params)
    })
    return h
  }

  private readonly editorApi: EditorApi = {
    sendClientRequest: async (uri: string, method: string, params: any): Promise<any> => {
      const client = this.client // clientProvider.findClient(uri)
      if (client != null) {
        try {
          const result = await client.sendRequest(method, params)
          return result
        } catch (ex: any) {
          console.log(`[InfoProvider]The Lean Server has stopped processing this file: ${ex.message}`)
        }
      }
      return undefined
    },
    subscribeServerNotifications: async (method) => {

      // NOTE(WN): For non-custom notifications we cannot call LanguageClient.onNotification
      // here because that *overwrites* the notification handler rather than registers an extra one.
      // So we have to add a bunch of event emitters to `LeanClient.`
      if (method === 'textDocument/publishDiagnostics') {
        const subscriptions: Disposable[] = []
        for (const client of [this.client] /* this.clientProvider.getClients() */) {
          subscriptions.push(this.subscribeDiagnosticsNotification(client!, method))
        }
        this.serverNotifSubscriptions.set(method, [1, subscriptions])
      }
    },

    subscribeClientNotifications: async (method) => {
      throw new Error('Function not implemented.')
    },
    insertText: async (text, kind, tdpp) => {
      let uri: Uri | undefined
      let pos: Position | undefined
      if (tdpp != null) {
        uri = p2cConverter.asUri(tdpp.textDocument.uri)
        pos = fromLanguageServerPosition(tdpp.position)
      }
      await this.handleInsertText(text, kind, uri, pos)
    },

    createRpcSession: async (uri) => {
      const client = this.client // this.clientProvider.findClient(uri)
      if (client == null) return ''
      const sessionId = await rpcConnect(client, uri)
      const session = new RpcSessionAtPos(client, sessionId, uri)
      this.rpcSessions.set(sessionId, session)
      return sessionId
    },
    unsubscribeServerNotifications: function (method: string): Promise<void> {
      throw new Error('Function not implemented.')
    },
    unsubscribeClientNotifications: function (method: string): Promise<void> {
      throw new Error('Function not implemented.')
    },
    copyToClipboard: function (text: string): Promise<void> {
      throw new Error('Function not implemented.')
    },
    applyEdit: function (te: ls.WorkspaceEdit): Promise<void> {
      throw new Error('Function not implemented.')
    },
    showDocument: function (show: ls.ShowDocumentParams): Promise<void> {
      throw new Error('Function not implemented.')
    },
    closeRpcSession: function (sessionId: string): Promise<void> {
      throw new Error('Function not implemented.')
    },
    sendClientNotification: function (uri: string, method: string, params: any): Promise<void> {
      throw new Error('Function not implemented.')
    }
  }

  constructor (private readonly myclient: LeanClient | undefined) {
    // this.clientProvider = provider
    this.client = myclient

    this.onClientAdded(this.client!)

    this.subscriptions.push(
      window.onDidChangeActiveTextEditor(async () => await this.sendPosition()),
      window.onDidChangeTextEditorSelection(async () => await this.sendPosition()),
      workspace.onDidChangeTextDocument(async () => {
        await this.sendPosition()
      })
    )
  }

  private async onClientAdded (client: LeanClient) {
    console.log(`[InfoProvider] Adding client`)

    this.clientSubscriptions.push(
      client.restarted(async () => {
        console.log('[InfoProvider] got client restarted event')
        
        await this.initInfoView(this.editor, client)
      })
    )
  }

  getApi () {
    return this.editorApi
  }

  async openPreview (editor: monaco.editor.IStandaloneCodeEditor, infoviewApi: InfoviewApi) {
    this.infoviewApi = infoviewApi
    this.editor = editor
    await this.initInfoView(editor, this.client!)
  }

  private async initInfoView (editor: monaco.editor.IStandaloneCodeEditor | undefined, client: LeanClient | null) {
    if (editor != null) {
      const loc = this.getLocation(editor)
      if (loc != null) {
        console.log('initialize infoview api')
        await this.infoviewApi?.initialize(loc)
      }
    }

    // The infoview gets information about file progress, diagnostics, etc.
    // by listening to notifications.  Send these notifications when the infoview starts
    // so that it has up-to-date information.
    if ((client?.initializeResult) != null) {
      await this.infoviewApi?.serverRestarted(client.initializeResult)
      await this.sendPosition()
    }
  }

  private getLocation (editor: monaco.editor.IStandaloneCodeEditor): ls.Location | undefined {
    if (!editor) return undefined
    const uri = editor.getModel()?.uri
    const selection = editor.getSelection()!
    return {
      uri: uri!.toString(),
      range: toLanguageServerRange(selection)
    }
  }

  private async sendPosition () {
    const editor = this.editor
    if (editor == null) return
    const loc = this.getLocation(editor)
    if (this.client.running){
      await this.infoviewApi?.changedCursorLocation(loc)
    }
  }

  private async handleInsertText (text: string, kind: TextInsertKind, uri?: Uri, pos?: monaco.Position) {
    if (this.editor == null) {
      return
    }
    pos = (pos != null) ? pos : this.editor.getSelection().getStartPosition()
    if (kind === 'above') {
      // in this case, assume that we actually want to insert at the same
      // indentation level as the neighboring text
      const spaces =  this.editor.getModel().getLineFirstNonWhitespaceColumn(pos.lineNumber) - 1
      const margin_str = [...Array(spaces).keys()].map(x => ' ').join('')
      let new_command = text.replace(/\n/g, '\n' + margin_str)
      new_command = `${margin_str}${new_command}\n`
      const insertPosition = monaco.Range.fromPositions({lineNumber: pos.lineNumber, column: 0})

      await this.editor.pushUndoStop()
      await this.editor.executeEdits(
        "infoview",
        [{ range: insertPosition, text: new_command, forceMoveMarkers: true }],
      )
    } else {
      if (pos != null) {
        await this.editor.pushUndoStop()
        await this.editor.executeEdits(
          "infoview",
          [{ range: monaco.Range.fromPositions(pos), text: text, forceMoveMarkers: true }],
        )
      }
    }
    this.editor.focus()
  }
}
