/* This file is based on `vscode-lean4/src/leanclient.ts` */

import {
  TextDocument, EventEmitter, Diagnostic,
  DocumentHighlight, Range, DocumentHighlightKind,
  Disposable, Uri, DiagnosticCollection,
  WorkspaceFolder, workspace
} from 'vscode'
import {
  DidChangeTextDocumentParams,
  DidCloseTextDocumentParams,
  InitializeResult,
  MonacoLanguageClient as LanguageClient,
  LanguageClientOptions,
  PublishDiagnosticsParams,
  CloseAction, ErrorAction, IConnectionProvider,
} from 'monaco-languageclient'
import * as monaco from 'monaco-editor/esm/vs/editor/editor.api.js'
import { State } from 'vscode-languageclient'
import * as ls from 'vscode-languageserver-protocol'

import { getElaborationDelay } from './config'
import { LeanFileProgressParams, LeanFileProgressProcessingInfo } from '@leanprover/infoview-api'
import { c2pConverter, p2cConverter, patchConverters } from './utils/converters'

const escapeRegExp = (s: string) => s.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')

export type ServerProgress = Map<Uri, LeanFileProgressProcessingInfo[]>

export function getFullRange (diag: Diagnostic): Range {
  return (diag as any)?.fullRange || diag.range
}

export class LeanClient implements Disposable {
  running: boolean = false
  private client: LanguageClient | undefined
  private noPrompt: boolean = false

  private readonly didChangeEmitter = new EventEmitter<DidChangeTextDocumentParams>()
  didChange = this.didChangeEmitter.event

  private readonly diagnosticsEmitter = new EventEmitter<PublishDiagnosticsParams>()
  diagnostics = this.diagnosticsEmitter.event

  private readonly didSetLanguageEmitter = new EventEmitter<string>()
  didSetLanguage = this.didSetLanguageEmitter.event

  private readonly didCloseEmitter = new EventEmitter<DidCloseTextDocumentParams>()
  didClose = this.didCloseEmitter.event

  private readonly customNotificationEmitter = new EventEmitter<{ method: string, params: any }>()
  /** Fires whenever a custom notification (i.e. one not defined in LSP) is received. */
  customNotification = this.customNotificationEmitter.event

  /** saved progress info in case infoview is opened, it needs to get all of it. */
  progress: ServerProgress = new Map()

  private readonly progressChangedEmitter = new EventEmitter<[string, LeanFileProgressProcessingInfo[]]>()
  progressChanged = this.progressChangedEmitter.event

  private readonly stoppedEmitter = new EventEmitter()
  stopped = this.stoppedEmitter.event

  private readonly restartedEmitter = new EventEmitter()
  restarted = this.restartedEmitter.event

  private readonly restartingEmitter = new EventEmitter()
  restarting = this.restartingEmitter.event

  private readonly restartedWorkerEmitter = new EventEmitter<string>()
  restartedWorker = this.restartedWorkerEmitter.event

  private readonly serverFailedEmitter = new EventEmitter<string>()
  serverFailed = this.serverFailedEmitter.event

  constructor (
    private readonly connectionProvider: IConnectionProvider,
    public readonly showRestartMessage: () => void) {

  }

  dispose (): void {
    if (this.client.isRunning()) {
      this.client.dispose()
    } else {
      this.client.onDidChangeState((ev) => {
        if (ev.newState == State.Running) {
          setTimeout(() => { // Wait for client to send `initialized` before `shutdown`
            this.client.dispose()
          }, 0)
        }
      })
    }
  }

  async restart (): Promise<void> {
    const startTime = Date.now()

    console.log('[LeanClient] Restarting Lean Server')
    if (this.isStarted()) {
      await this.stop()
    }

    this.restartingEmitter.fire(undefined)

    const clientOptions: LanguageClientOptions = {
      // use a language id as a document selector
      documentSelector: ['lean4'],
      initializationOptions: {
        editDelay: getElaborationDelay(), hasWidgets: true
      },
      connectionOptions: {
        maxRestartCount: 0,
        cancellationStrategy: undefined as any
      },
      // disable the default error handler
      errorHandler: {
        error: () => { this.showRestartMessage(); return { action: ErrorAction.Continue }},
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

    let insideRestart = true
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
          if (!insideRestart) {
            this.restartedEmitter.fire(undefined)
          }
        } else if (s.newState === State.Stopped) {
          this.running = false
          console.log('[LeanClient] has stopped or it failed to start')
          if (!this.noPrompt) {
            // only raise this event and show the message if we are not the ones
            // who called the stop() method.
            this.stoppedEmitter.fire({ message: 'Lean server has stopped.', reason: '' })
          }
        }
      })
      await this.client.start()
      this.running = true
    } catch (error) {
      console.log(error)
      this.serverFailedEmitter.fire('' + error)
      insideRestart = false
      return
    }

    // HACK(WN): Register a default notification handler to fire on custom notifications.
    // A mechanism to do this is provided in vscode-jsonrpc. One can register a `StarNotificationHandler`
    // here: https://github.com/microsoft/vscode-languageserver-node/blob/b2fc85d28a1a44c22896559ee5f4d3ba37a02ef5/jsonrpc/src/common/connection.ts#L497
    // which fires on any LSP notifications not in the standard, for example the `$/lean/..` ones.
    // However this mechanism is not exposed in vscode-languageclient, so we hack around its implementation.
    const starHandler = (method: string, params_: any) => {
      if (method === '$/lean/fileProgress' && (this.client != null)) {
        const params = params_ as LeanFileProgressParams
        const uri = p2cConverter.asUri(params.textDocument.uri)
        this.progressChangedEmitter.fire([uri.toString(), params.processing])
        // save the latest progress on this Uri in case infoview needs it later.
        this.progress.set(uri, params.processing)
      }

      this.customNotificationEmitter.fire({ method, params: params_ })
    }
    // eslint-disable-next-line @typescript-eslint/no-unsafe-argument
    this.client.onNotification(starHandler as any, () => {})

    this.restartedEmitter.fire(undefined)
    insideRestart = false
  }

  async start (): Promise<void> {
    return await this.restart()
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

  async stop (): Promise<void> {
    // assert(() => this.isStarted())
    if ((this.client != null) && this.running) {
      this.noPrompt = true
      try {
        // some timing conditions can happen while running unit tests that cause
        // this to throw an exception which then causes those tests to fail.
        await this.client.stop()
      } catch (e) {
        console.log(`[LeanClient] Error stopping language client: ${e}`)
      }
    }

    this.noPrompt = false
    this.progress = new Map()
    this.client = undefined
    this.running = false
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
    this.restartedWorkerEmitter.fire(uri)
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

  async getDiagnosticParams (uri: Uri, diagnostics: readonly Diagnostic[]): Promise<PublishDiagnosticsParams> {
    const params: PublishDiagnosticsParams = {
      uri: c2pConverter.asUri(uri),
      diagnostics: await c2pConverter.asDiagnostics(diagnostics as Diagnostic[])
    }
    return params
  }

  getDiagnostics (): DiagnosticCollection | undefined {
    return this.running ? this.client?.diagnostics : undefined
  }

  get initializeResult (): InitializeResult | undefined {
    return this.running ? this.client?.initializeResult : undefined
  }

}
