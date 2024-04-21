/* This file is based on `vscode-lean4/vscode-lean4/src/infoview.ts ` */

import { Disposable } from 'vscode'
import * as ls from 'vscode-languageserver-protocol'

import { LeanClient } from './client'

import { EditorApi, InfoviewApi, RpcConnected, RpcKeepAliveParams } from '@leanprover/infoview-api'

import * as monaco from 'monaco-editor/esm/vs/editor/editor.api.js'

function toLanguageServerRange (range: monaco.Range): ls.Range {
  return {
    start: { line: range.startLineNumber - 1, character: range.startColumn - 1},
    end: { line: range.endLineNumber - 1, character: range.endColumn - 1}
  }
}

export class InfoProvider implements Disposable {

  private infoviewApi?: InfoviewApi
  private editor?: monaco.editor.IStandaloneCodeEditor

  public readonly client?: LeanClient

  private readonly editorApi: EditorApi = {
    createRpcSession: async (uri) => {
      const result: RpcConnected = await this.client.sendRequest('$/lean/rpc/connect', { uri })
      return result.sessionId
    },
    sendClientRequest: async (uri: string, method: string, params: any): Promise<any> => {
      return await this.client.sendRequest(method, params)
    },
    subscribeServerNotifications: async (method) => {

      if (method === 'textDocument/publishDiagnostics') {
        for (const client of [this.client] /* this.clientProvider.getClients() */) {
          client.diagnostics((params) => this.infoviewApi?.gotServerNotification(method, params))
        }
      }
    },

    subscribeClientNotifications: async (method) => {
      throw new Error('Function not implemented.')
    },
    insertText: async (text, kind, tdpp) => {
      throw new Error('Function not implemented.')
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

  constructor (private readonly _client: LeanClient | undefined) {

    this.client = _client

    this.client.restarted(() => this.initInfoView(this.editor))
  }

  getApi () {
    return this.editorApi
  }

  async openPreview (editor: monaco.editor.IStandaloneCodeEditor, infoviewApi: InfoviewApi) {
    this.infoviewApi = infoviewApi
    this.editor = editor
    await this.initInfoView(editor)
  }

  private async initInfoView (editor: monaco.editor.IStandaloneCodeEditor | undefined) {
    
    const uri = editor.getModel()?.uri
    const selection = editor.getSelection()!
    const loc = { uri: uri!.toString(), range: toLanguageServerRange(selection) }

    await this.infoviewApi?.initialize(loc)

    // The infoview gets information about file progress, diagnostics, etc. by listening to notifications.
    // Send these notifications when the infoview starts so that it has up-to-date information.
    await this.infoviewApi?.serverRestarted(this.client?.initializeResult)
  }

}
