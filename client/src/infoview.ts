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
  public readonly editorApi: EditorApi = {
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
          client.diagnosticsEmitter.event((params) => this.infoviewApi.gotServerNotification(method, params))
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

    this.client.restartedEmitter.event(() => this.initInfoView())
  }

  async setInfoviewApi (infoviewApi: InfoviewApi) {
    this.infoviewApi = infoviewApi
  }

  async initInfoView () {
    
    const uri = this.editor.getModel().uri.toString()
    const range = { start: { line: 0, character: 0 }, end: { line: 0, character: 0 } }
    await this.infoviewApi.initialize({ uri, range })
    await this.infoviewApi.serverRestarted(this.client.initializeResult)
  }
}
