/* This file is based on `vscode-lean4/src/leanclient.ts` */

import { EventEmitter, Disposable } from 'vscode'
import * as ls from 'vscode-languageserver-protocol'

import { DidChangeTextDocumentParams, InitializeResult, MonacoLanguageClient, LanguageClientOptions, PublishDiagnosticsParams, IConnectionProvider } from 'monaco-languageclient'

import { c2pConverter, patchConverters } from './utils'

const escapeRegExp = (s: string) => s.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')

export class LeanClient implements Disposable {
  private client: MonacoLanguageClient | undefined

  private readonly didChangeEmitter = new EventEmitter<DidChangeTextDocumentParams>()
  didChange = this.didChangeEmitter.event

  private readonly diagnosticsEmitter = new EventEmitter<PublishDiagnosticsParams>()
  diagnostics = this.diagnosticsEmitter.event

  private readonly restartedEmitter = new EventEmitter()
  restarted = this.restartedEmitter.event

  constructor (private readonly connectionProvider: IConnectionProvider) {

  }

  async restart (project): Promise<void> {

    console.log(`[LeanClient] Restarting Lean Server with project ${project}`)

    const clientOptions: LanguageClientOptions = {
      // use a language id as a document selector
      documentSelector: ['lean4'],
      workspaceFolder: {uri: "hello"},
      middleware: {
        handleDiagnostics: (uri, diagnostics, next) => {
          next(uri, diagnostics)
          if (this.client == null) return
          const uri_ = c2pConverter.asUri(uri)
          const diagnostics_ = []
          for (const d of diagnostics) {
            const d_: ls.Diagnostic = {
              ...c2pConverter.asDiagnostic(d)
            }
            diagnostics_.push(d_)
          }
          this.diagnosticsEmitter.fire({ uri: uri_, diagnostics: diagnostics_ })
        },
      }
    }
    if (!this.client) {
      this.client = new MonacoLanguageClient({
        id: 'lean4',
        name: 'Lean 4',
        clientOptions,
        connectionProvider: this.connectionProvider
      })
    }

    patchConverters(this.client.protocol2CodeConverter, this.client.code2ProtocolConverter)

    await this.client.start()

    this.restartedEmitter.fire({project: project})
  }

  // eslint-disable-next-line @typescript-eslint/explicit-module-boundary-types
  async sendRequest (method: string, params: any): Promise<any> {
    return this.client != null
      ? await this.client.sendRequest(method, params)
      : await new Promise<any>((_, reject) => { reject('Client is not running') })
  }

  // eslint-disable-next-line @typescript-eslint/explicit-module-boundary-types
  sendNotification (method: string, params: any): Promise<void> | undefined {
    return this.client.sendNotification(method, params)
  }

  get initializeResult (): InitializeResult | undefined {
    return this.client?.initializeResult
  }

}
