/* This file is based on `vscode-lean4/vscode-lean4/src/infoview.ts ` */

import { Disposable } from 'vscode'
import * as ls from 'vscode-languageserver-protocol'

import { LeanClient } from './client'

import { EditorApi, InfoviewApi, RpcConnected } from '@leanprover/infoview-api'

import * as monaco from 'monaco-editor/esm/vs/editor/editor.api.js'

export class InfoProvider implements Disposable {

  private infoviewApi: InfoviewApi
  private editor: monaco.editor.IStandaloneCodeEditor

  public readonly client: LeanClient

  private readonly editorApi: EditorApi = {
    createRpcSession: async (uri) => {
      const result: RpcConnected = await this.client.sendRequest('$/lean/rpc/connect', { uri })
      return result.sessionId
    },
    sendClientRequest: async (_uri: string, method: string, params: any): Promise<any> => {
      return await this.client.sendRequest(method, params)
    },
    subscribeServerNotifications: async (method) => {

      if (method === 'textDocument/publishDiagnostics') {
        for (const client of [this.client]) {
          client.diagnostics((params) => this.infoviewApi?.gotServerNotification(method, params))
        }
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

    this.client.restarted(() => this.initInfoView())
  }

  getEditorApi () {
    return this.editorApi
  }

  async openPreview (infoviewApi: InfoviewApi) {
    this.infoviewApi = infoviewApi
    
    await this.initInfoView()
  }

  private async initInfoView () {
    
    const uri = this.editor.getModel()?.uri
    const selection = this.editor.getSelection()!
    const range = {
      start: { line: selection.startLineNumber - 1, character: selection.startColumn - 1},
      end: { line: selection.endLineNumber - 1, character: selection.endColumn - 1}
    }
    const loc = { uri: uri!.toString(), range }

    await this.infoviewApi?.initialize(loc)

    // The infoview gets information about file progress, diagnostics, etc. by listening to notifications.
    // Send these notifications when the infoview starts so that it has up-to-date information.
    await this.infoviewApi?.serverRestarted(this.client?.initializeResult)
  }

}
