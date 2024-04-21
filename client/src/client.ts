/* This file is based on `vscode-lean4/src/leanclient.ts` */

import { EventEmitter, Disposable } from 'vscode'

import { InitializeResult, MonacoLanguageClient, LanguageClientOptions, PublishDiagnosticsParams, IConnectionProvider } from 'monaco-languageclient'

import { toSocket, WebSocketMessageWriter, WebSocketMessageReader } from 'vscode-ws-jsonrpc';

import { createConverter } from 'vscode-languageclient/lib/common/codeConverter'

const c2pConverter = createConverter(undefined)

export class LeanClient implements Disposable {
  private client: MonacoLanguageClient | undefined

  private readonly diagnosticsEmitter = new EventEmitter<PublishDiagnosticsParams>()
  diagnostics = this.diagnosticsEmitter.event

  private readonly restartedEmitter = new EventEmitter()
  restarted = this.restartedEmitter.event

  async start (project): Promise<void> {

    const clientOptions: LanguageClientOptions = {
      documentSelector: ['lean4'],
      middleware: {
        handleDiagnostics: (uri, diagnostics, next) => {
          next(uri, diagnostics)

          const diagnostics_ = diagnostics.map(d => c2pConverter.asDiagnostic(d))
          this.diagnosticsEmitter.fire({ uri: c2pConverter.asUri(uri), diagnostics: diagnostics_ })
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
    
    this.client = new MonacoLanguageClient({ id: 'lean4', name: 'Lean 4', clientOptions, connectionProvider })
    await this.client.start()

    this.restartedEmitter.fire({ project })
  }

  async sendRequest (method: string, params: any): Promise<any> {
    return await this.client.sendRequest(method, params)
  }

  sendNotification (method: string, params: any): Promise<void> | undefined {
    return this.client.sendNotification(method, params)
  }

  get initializeResult (): InitializeResult | undefined {
    return this.client.initializeResult
  }

}
