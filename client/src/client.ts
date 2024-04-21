/* This file is based on `vscode-lean4/src/leanclient.ts` */

import { TextDocument, EventEmitter, DocumentHighlight, Range, DocumentHighlightKind, Disposable } from 'vscode'
import { State } from 'vscode-languageclient'
import * as ls from 'vscode-languageserver-protocol'

import {
  DidChangeTextDocumentParams,
  DidCloseTextDocumentParams,
  InitializeResult,
  MonacoLanguageClient as LanguageClient,
  LanguageClientOptions,
  PublishDiagnosticsParams,
  CloseAction, ErrorAction, IConnectionProvider,
} from 'monaco-languageclient'

import { c2pConverter, patchConverters } from './utils'

const escapeRegExp = (s: string) => s.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')

export class LeanClient implements Disposable {
  running: boolean = false
  private client: LanguageClient | undefined

  private readonly didChangeEmitter = new EventEmitter<DidChangeTextDocumentParams>()
  didChange = this.didChangeEmitter.event

  private readonly diagnosticsEmitter = new EventEmitter<PublishDiagnosticsParams>()
  diagnostics = this.diagnosticsEmitter.event

  private readonly restartedEmitter = new EventEmitter()
  restarted = this.restartedEmitter.event

  // private readonly restartedWorkerEmitter = new EventEmitter<string>()
  // restartedWorker = this.restartedWorkerEmitter.event

  constructor (private readonly connectionProvider: IConnectionProvider) {

  }

  async restart (project): Promise<void> {
    const startTime = Date.now()

    console.log(`[LeanClient] Restarting Lean Server with project ${project}`)

    const clientOptions: LanguageClientOptions = {
      // use a language id as a document selector
      documentSelector: ['lean4'],
      workspaceFolder: {uri: "hello"},
      initializationOptions: {
        editDelay: 200,
        hasWidgets: true,
      },
      connectionOptions: {
        maxRestartCount: 0,
        cancellationStrategy: undefined as any
      },
      // disable the default error handler
      errorHandler: {
        error: () => ({ action: ErrorAction.Continue }),
        closed: () => ({ action: CloseAction.DoNotRestart })
      },
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

        // Closing does not work properly, so we deactivate it here:
        didClose: async (data, next) => {},

        didChange: async (data, next) => {
          await next(data)
          if (!this.running || (this.client == null)) return // there was a problem starting lean server.
          const params = c2pConverter.asChangeTextDocumentParams(data)
          this.didChangeEmitter.fire(params)
        },

        provideDocumentHighlights: async (doc, pos, ctok, next) => {
          const leanHighlights = await next(doc, pos, ctok)
          if (leanHighlights?.length) return leanHighlights

          // vscode doesn't fall back to textual highlights,
          // so we need to do that manually
          await new Promise((res) => setTimeout(res, 250))
          if (ctok.isCancellationRequested) return

          const wordRange = doc.getWordRangeAtPosition(pos)
          if (wordRange == null) return
          const word = doc.getText(wordRange)

          const highlights: DocumentHighlight[] = []
          const text = doc.getText()
          const nonWordPattern = '[`~@$%^&*()-=+\\[{\\]}⟨⟩⦃⦄⟦⟧⟮⟯‹›\\\\|;:\",./\\s]|^|$'
          const regexp = new RegExp(`(?<=${nonWordPattern})${escapeRegExp(word)}(?=${nonWordPattern})`, 'g')
          for (const match of text.matchAll(regexp)) {
            const start = doc.positionAt(match.index ?? 0)
            highlights.push({
              range: new Range(start, start.translate(0, match[0].length)),
              kind: DocumentHighlightKind.Text
            })
          }

          return highlights
        }
      }
    }
    if (!this.client) {
      this.client = new LanguageClient({
        id: 'lean4',
        name: 'Lean 4',
        clientOptions,
        connectionProvider: this.connectionProvider
      })
    }

    // HACK: Prevent monaco from panicking when the Lean server crashes
    this.client.handleFailedRequest = (type, token: any, error: any, defaultValue, showNotification?: boolean) => {
      return defaultValue
    }

    patchConverters(this.client.protocol2CodeConverter, this.client.code2ProtocolConverter)
    try {
      this.client.onDidChangeState(async (s) => {
        // see https://github.com/microsoft/vscode-languageserver-node/issues/825
        if (s.newState === State.Starting) {
          console.log('[LeanClient] starting')
        } else if (s.newState === State.Running) {
          const end = Date.now()
          console.log(`[LeanClient] running, started in ${end - startTime} ms`)
          this.running = true // may have been auto restarted after it failed.
        } else if (s.newState === State.Stopped) {
          this.running = false
          console.log('[LeanClient] has stopped or it failed to start')
        }
      })
      await this.client.start()
      this.running = true
    } catch (error) {
      console.log(error)
      return
    }

    this.restartedEmitter.fire({project: project})
  }

  isStarted (): boolean {
    return this.client !== undefined
  }

  isRunning (): boolean {
    if (this.client != null) {
      return this.running
    }
    return false
  }

  async restartFile (doc: TextDocument): Promise<void> {
    if (!this.running) return // there was a problem starting lean server.

    const uri = doc.uri.toString()
    console.log(`[LeanClient] Restarting File: ${uri}`)
    // This causes a text document version number discontinuity. In
    // (didChange (oldVersion) => restartFile => didChange (newVersion))
    // the client emits newVersion = oldVersion + 1, despite the fact that the
    // didOpen packet emitted below initializes the version number to be 1.
    // This is not a problem though, since both client and server are fine
    // as long as the version numbers are monotonous.
    void this.client?.sendNotification('textDocument/didClose', {
      textDocument: {
        uri
      }
    })
    void this.client?.sendNotification('textDocument/didOpen', {
      textDocument: {
        uri,
        languageId: 'lean4',
        version: 1,
        text: doc.getText()
      }
    })
    // this.restartedWorkerEmitter.fire(uri)
  }

  // eslint-disable-next-line @typescript-eslint/explicit-module-boundary-types
  async sendRequest (method: string, params: any): Promise<any> {
    return this.running && (this.client != null)
      ? await this.client.sendRequest(method, params)
      : await new Promise<any>((_, reject) => { reject('Client is not running') })
  }

  // eslint-disable-next-line @typescript-eslint/explicit-module-boundary-types
  sendNotification (method: string, params: any): Promise<void> | undefined {
    return this.running && (this.client != null) ? this.client.sendNotification(method, params) : undefined
  }

  get initializeResult (): InitializeResult | undefined {
    return this.running ? this.client?.initializeResult : undefined
  }

}
