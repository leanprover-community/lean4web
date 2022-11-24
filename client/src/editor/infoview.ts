/* This file is based on `vscode-lean4/vscode-lean4/src/infoview.ts ` */

import { join } from 'path'
import {
  commands, Disposable, DocumentSelector,
  ExtensionContext, languages,
  Selection, TextEditor, TextEditorRevealType,
  Uri, ViewColumn, WebviewPanel, window, workspace, env, Position, WorkspaceEdit
} from 'vscode'
import {
  EditorApi, InfoviewApi, LeanFileProgressParams, TextInsertKind,
  RpcConnectParams, RpcConnected, RpcKeepAliveParams, RpcErrorCode
} from '@leanprover/infoview-api'
import { LeanClient } from './leanclient'
// import {
//   getEditorLineHeight, getInfoViewAllErrorsOnLine, getInfoViewAutoOpen, getInfoViewAutoOpenShowGoal,
//   getInfoViewStyle, minIfProd, prodOrDev
// } from './config'
// import { Rpc } from './rpc'
// import { LeanClientProvider } from './utils/clientProvider'
import * as ls from 'vscode-languageserver-protocol'
import { c2pConverter, fromLanguageServerPosition, fromLanguageServerRange, p2cConverter, toLanguageServerRange } from './utils/converters'
// import { logger } from './utils/logger'
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

  dispose () {
    if (this.keepAliveInterval != null) clearInterval(this.keepAliveInterval)
    // TODO: at this point we could close the session
  }
}

export class InfoProvider implements Disposable {
  /** Instance of the panel, if it is open. Otherwise `undefined`. */
  private infoviewApi?: InfoviewApi
  private editor?: monaco.editor.IStandaloneCodeEditor
  private readonly subscriptions: Disposable[] = []
  private readonly clientSubscriptions: Disposable[] = []

  private readonly stylesheet: string = ''
  private readonly autoOpened: boolean = false
  public readonly client?: LeanClient
  // private readonly clientProvider: LeanClientProvider

  // Subscriptions are counted and only disposed of when count becomes 0.
  private readonly serverNotifSubscriptions: Map<string, [number, Disposable[]]> = new Map()
  private readonly clientNotifSubscriptions: Map<string, [number, Disposable[]]> = new Map()

  private rpcSessions: Map<string, RpcSessionAtPos> = new Map()

  // the key is the LeanClient.getWorkspaceFolder()
  private readonly clientsFailed: Map<string, any> = new Map()

  // the key is the uri of the file who's worker has failed.
  private readonly workersFailed: Map<string, any> = new Map()

  private subscribeDidChangeNotification (client: LeanClient, method: string) {
    const h = client.didChange((params) => {
      void this.infoviewApi?.sentClientNotification(method, params)
    })
    return h
  }

  private subscribeDidCloseNotification (client: LeanClient, method: string) {
    const h = client.didClose((params) => {
      void this.infoviewApi?.sentClientNotification(method, params)
    })
    return h
  }

  private subscribeDiagnosticsNotification (client: LeanClient, method: string) {
    const h = client.diagnostics((params) => {
      void this.infoviewApi?.gotServerNotification(method, params)
    })
    return h
  }

  private subscribeCustomNotification (client: LeanClient, method: string) {
    const h = client.customNotification(({ method: thisMethod, params }) => {
      if (thisMethod !== method) return
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
          if (ex.code === RpcErrorCode.WorkerCrashed) {
            // ex codes related with worker exited or crashed
            console.log(`[InfoProvider]The Lean Server has stopped processing this file: ${ex.message}`)
            await this.onWorkerStopped(uri, client, { message: 'The Lean Server has stopped processing this file: ', reason: ex.message as string })
          }
          throw ex
        }
      }
      return undefined
    },
    sendClientNotification: async (uri: string, method: string, params: any): Promise<void> => {
      const client = this.client // this.clientProvider.findClient(uri)
      if (client != null) {
        await client.sendNotification(method, params)
      }
    },
    subscribeServerNotifications: async (method) => {
      const el = this.serverNotifSubscriptions.get(method)
      if (el != null) {
        const [count, h] = el
        this.serverNotifSubscriptions.set(method, [count + 1, h])
        return
      }

      // NOTE(WN): For non-custom notifications we cannot call LanguageClient.onNotification
      // here because that *overwrites* the notification handler rather than registers an extra one.
      // So we have to add a bunch of event emitters to `LeanClient.`
      if (method === 'textDocument/publishDiagnostics') {
        const subscriptions: Disposable[] = []
        for (const client of [this.client]/* this.clientProvider.getClients() */) {
          subscriptions.push(this.subscribeDiagnosticsNotification(client!, method))
        }
        this.serverNotifSubscriptions.set(method, [1, subscriptions])
      } else if (method.startsWith('$')) {
        const subscriptions: Disposable[] = []
        for (const client of [this.client]/* this.clientProvider.getClients() */) {
          subscriptions.push(this.subscribeCustomNotification(client!, method))
        }
        this.serverNotifSubscriptions.set(method, [1, subscriptions])
      } else {
        throw new Error(`subscription to ${method} server notifications not implemented`)
      }
    },
    unsubscribeServerNotifications: async (method) => {
      const el = this.serverNotifSubscriptions.get(method)
      if (el == null) throw new Error(`trying to unsubscribe from '${method}' with no active subscriptions`)
      const [count, subscriptions] = el
      if (count === 1) {
        for (const h of subscriptions) {
          h.dispose()
        }
        this.serverNotifSubscriptions.delete(method)
      } else {
        this.serverNotifSubscriptions.set(method, [count - 1, subscriptions])
      }
    },

    subscribeClientNotifications: async (method) => {
      const el = this.clientNotifSubscriptions.get(method)
      if (el != null) {
        const [count, d] = el
        this.clientNotifSubscriptions.set(method, [count + 1, d])
        return
      }

      if (method === 'textDocument/didChange') {
        const subscriptions: Disposable[] = []
        for (const client of [this.client]/* this.clientProvider.getClients() */) {
          subscriptions.push(this.subscribeDidChangeNotification(client!, method))
        }
        this.clientNotifSubscriptions.set(method, [1, subscriptions])
      } else if (method === 'textDocument/didClose') {
        const subscriptions: Disposable[] = []
        for (const client of [this.client]/* this.clientProvider.getClients() */) {
          subscriptions.push(this.subscribeDidCloseNotification(client!, method))
        }
        this.clientNotifSubscriptions.set(method, [1, subscriptions])
      } else {
        throw new Error(`Subscription to '${method}' client notifications not implemented`)
      }
    },

    unsubscribeClientNotifications: async (method) => {
      const el = this.clientNotifSubscriptions.get(method)
      if (el == null) throw new Error(`trying to unsubscribe from '${method}' with no active subscriptions`)
      const [count, subscriptions] = el
      if (count === 1) {
        for (const d of subscriptions) {
          d.dispose()
        }
        this.clientNotifSubscriptions.delete(method)
      } else {
        this.clientNotifSubscriptions.set(method, [count - 1, subscriptions])
      }
    },
    copyToClipboard: async (text) => {
      await env.clipboard.writeText(text)
      await window.showInformationMessage(`Copied to clipboard: ${text}`)
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
    applyEdit: async (e: ls.WorkspaceEdit) => {
      const we = await p2cConverter.asWorkspaceEdit(e)
      await workspace.applyEdit(we)
    },
    showDocument: async (show) => {
      void this.revealEditorSelection(
        Uri.parse(show.uri),
        fromLanguageServerRange(show.selection)
      )
    },

    createRpcSession: async uri => {
      const client = this.client // this.clientProvider.findClient(uri)
      if (client == null) return ''
      const sessionId = await rpcConnect(client, uri)
      const session = new RpcSessionAtPos(client, sessionId, uri)
      // if (this.webviewPanel == null) {
      //   session.dispose()
      //   throw Error('infoview disconnect while connecting to RPC session')
      // } else {
      this.rpcSessions.set(sessionId, session)
      return sessionId
      // }
    },
    closeRpcSession: async sessionId => {
      const session = this.rpcSessions.get(sessionId)
      if (session != null) {
        this.rpcSessions.delete(sessionId)
        session.dispose()
      }
    }
  }

  constructor (private readonly myclient: LeanClient | undefined/*, private readonly leanDocs: DocumentSelector, private readonly context: ExtensionContext */) {
    // this.clientProvider = provider
    this.client = myclient
    this.updateStylesheet()

    this.onClientAdded(this.client!)

    // provider.clientAdded((client) => {
    //   void this.onClientAdded(client)
    // })

    // provider.clientRemoved((client) => {
    //   void this.onClientRemoved(client)
    // })

    // provider.clientStopped(([client, activeClient, reason]) => {
    //   void this.onActiveClientStopped(client, activeClient, reason)
    // })

    this.subscriptions.push(
      window.onDidChangeActiveTextEditor(async () => await this.sendPosition()),
      window.onDidChangeTextEditorSelection(async () => await this.sendPosition()),
      workspace.onDidChangeConfiguration(async (_e) => {
        // regression; changing the style needs a reload. :/
        this.updateStylesheet()
        await this.sendConfig()
      }),
      workspace.onDidChangeTextDocument(async () => {
        await this.sendPosition()
      })
      // commands.registerTextEditorCommand('lean4.displayGoal', async (editor) => await this.openPreview(editor, this.infoviewApi!)),
      // commands.registerTextEditorCommand('lean4.toggleInfoview', async (editor) => await this.toggleInfoview(editor)),
      // commands.registerTextEditorCommand('lean4.displayList', async (editor) => {
      //   await this.openPreview(editor, this.infoviewApi!)
      //   await this.infoviewApi?.requestedAction({ kind: 'toggleAllMessages' })
      // }),
      // commands.registerTextEditorCommand('lean4.infoView.copyToComment',
      //   () => this.infoviewApi?.requestedAction({ kind: 'copyToComment' })),
      // commands.registerCommand('lean4.infoView.toggleUpdating', () =>
      //   this.infoviewApi?.requestedAction({ kind: 'togglePaused' })),
      // commands.registerTextEditorCommand('lean4.infoView.toggleStickyPosition',
      //   () => this.infoviewApi?.requestedAction({ kind: 'togglePin' }))
    )
  }

  private async onClientRestarted (client: LeanClient) {
    // if we already have subscriptions for a previous client, we need to also
    // subscribe to the same things on this new client.
    for (const [method, [count, subscriptions]] of this.clientNotifSubscriptions) {
      if (method === 'textDocument/didChange') {
        subscriptions.push(this.subscribeDidChangeNotification(client, method))
      } else if (method === 'textDocument/didClose') {
        subscriptions.push(this.subscribeDidCloseNotification(client, method))
      }
    }

    for (const [method, [count, subscriptions]] of this.serverNotifSubscriptions) {
      if (method === 'textDocument/publishDiagnostics') {
        subscriptions.push(this.subscribeDiagnosticsNotification(client, method))
      } else if (method.startsWith('$')) {
        subscriptions.push(this.subscribeCustomNotification(client, method))
      }
    }

    // await this.infoviewApi?.serverStopped('client restarted') // clear any server stopped state
    const folder = client.getWorkspaceFolder()
    for (const uri of this.workersFailed.keys()) {
      if (uri.startsWith(folder)) {
        this.workersFailed.delete(uri)
      }
    }
    if (this.clientsFailed.has(folder)) {
      this.clientsFailed.delete(folder)
    }
    await this.initInfoView(this.editor, client)
  }

  private async onClientAdded (client: LeanClient) {
    console.log(`[InfoProvider] Adding client for workspace: ${client.getWorkspaceFolder()}`)

    this.clientSubscriptions.push(
      client.restarted(async () => {
        console.log('[InfoProvider] got client restarted event')
        // This event is triggered both the first time the server starts
        // as well as when the server restarts.

        this.clearRpcSessions(client)

        // Need to fully re-initialize this newly restarted client with all the
        // existing subscriptions and resend position info and so on so the
        // infoview updates properly.
        await this.onClientRestarted(client)
      }),
      client.restartedWorker(async (uri) => {
        console.log('[InfoProvider] got worker restarted event')
        await this.onWorkerRestarted(uri)
      }),
      client.didSetLanguage(() => this.onLanguageChanged())
    )

    // Note that when new client is first created it still fires client.restarted
    // event, so all onClientRestarted can happen there so we don't do it twice.
  }

  async onWorkerRestarted (uri: string): Promise<void> {
    await this.infoviewApi?.serverStopped(undefined) // clear any server stopped state
    if (this.workersFailed.has(uri)) {
      this.workersFailed.delete(uri)
      console.log('[InfoProvider] Restarting worker for file: ' + uri)
    }
    await this.sendPosition()
  }

  async onWorkerStopped (uri: string, client: LeanClient, reason: any) {
    await this.infoviewApi?.serverStopped(reason)

    if (!this.workersFailed.has(uri)) {
      this.workersFailed.set(uri, reason)
    }
    console.log(`[InfoProvider]client crashed: ${uri}`)
    await client.showRestartMessage()
  }

  onClientRemoved (client: LeanClient) {
    // todo: remove subscriptions for this client...
  }

  async onActiveClientStopped (client: LeanClient, activeClient: boolean, reason: any) {
    // Will show a message in case the active client stops
    // add failed client into a list (will be removed in case the client is restarted)
    if (activeClient) {
      // means that client and active client are the same and just show the error message
      await this.infoviewApi?.serverStopped(reason)
    }

    console.log(`[InfoProvider] client stopped: ${client.getWorkspaceFolder()}`)

    // remember this client is in a stopped state
    const key = client.getWorkspaceFolder()
    if (key) {
      await this.sendPosition()
      if (!this.clientsFailed.has(key)) {
        this.clientsFailed.set(key, reason)
      }
      console.log(`[InfoProvider] client stopped: ${key}`)
      await client.showRestartMessage()
    }
  }

  dispose (): void {
    // active client is changing.
    this.clearNotificationHandlers()
    this.clearRpcSessions(null)
    for (const s of this.clientSubscriptions) { s.dispose() }
    for (const s of this.subscriptions) { s.dispose() }
  }

  isOpen (): boolean {
    return /* this.webviewPanel?.visible === */ true
  }

  async runTestScript (javaScript: string): Promise<void> {
    if (this.infoviewApi != null) {
      return await this.infoviewApi.runTestScript(javaScript)
    } else {
      throw new Error('Cannot run test script, infoview is closed.')
    }
  }

  async getHtmlContents (): Promise<string> {
    if (this.infoviewApi != null) {
      return await this.infoviewApi.getInfoviewHtml()
    } else {
      throw new Error('Cannot retrieve infoview HTML, infoview is closed.')
    }
  }

  async sleep (ms: number) {
    return await new Promise((resolve) => setTimeout(resolve, ms))
  }

  async toggleAllMessages (): Promise<void> {
    if (this.infoviewApi != null) {
      await this.infoviewApi.requestedAction({ kind: 'toggleAllMessages' })
    }
  }

  private updateStylesheet () {
    // // Here we add extra CSS variables which depend on the editor configuration,
    // // but are not exposed by default.
    // // Ref: https://code.visualstudio.com/api/extension-guides/webview#theming-webview-content

    // const extraCSS = `
    //         html {
    //             --vscode-editor-line-height: ${getEditorLineHeight()}px;
    //         }
    //     `
    // const configCSS = getInfoViewStyle()
    // this.stylesheet = extraCSS + configCSS
  }

  private async autoOpen (): Promise<boolean> {
    // if ((this.webviewPanel == null) && !this.autoOpened && getInfoViewAutoOpen() && (window.activeTextEditor != null)) {
    //   // only auto-open for lean files, not for markdown.
    //   if (languages.match(this.leanDocs, window.activeTextEditor.document)) {
    //     // remember we've auto opened during this session so if user closes it it remains closed.
    //     this.autoOpened = true
    //     await this.openPreview(window.activeTextEditor)
    //     return true
    //   }
    // }
    return false
  }

  private clearNotificationHandlers () {
    for (const [, [, subscriptions]] of this.clientNotifSubscriptions) { for (const h of subscriptions) h.dispose() }
    this.clientNotifSubscriptions.clear()
    for (const [, [, subscriptions]] of this.serverNotifSubscriptions) { for (const h of subscriptions) h.dispose() }
    this.serverNotifSubscriptions.clear()
  }

  private clearRpcSessions (client: LeanClient | null) {
    const remaining = new Map()
    for (const [sessionId, sess] of this.rpcSessions) {
      if (client === null || sess.client === client) {
        sess.dispose()
      } else {
        remaining.set(sessionId, sess)
      }
    }
    this.rpcSessions = remaining
  }

  private async toggleInfoview (editor: TextEditor) {
    // if (this.webviewPanel != null) {
    //   this.webviewPanel.dispose()
    //   // the onDispose handler sets this.webviewPanel = undefined
    // } else {
    //   return await this.openPreview(editor)
    // }
  }

  getApi () {
    return this.editorApi
  }

  async openPreview (editor: monaco.editor.IStandaloneCodeEditor, infoviewApi: InfoviewApi) {
    this.infoviewApi = infoviewApi
    this.editor = editor
    // let column = editor && editor.viewColumn ? editor.viewColumn + 1 : ViewColumn.Two
    // if (column === 4) { column = ViewColumn.Three }
    // if (this.webviewPanel != null) {
    //   this.webviewPanel.reveal(column, true)
    // } else {
    //   const webviewPanel = window.createWebviewPanel('lean4', 'Lean Infoview',
    //     { viewColumn: column, preserveFocus: true },
    //     {
    //       enableFindWidget: true,
    //       retainContextWhenHidden: true,
    //       enableScripts: true,
    //       enableCommandUris: true
    //     }) as WebviewPanel & { rpc: Rpc, api: InfoviewApi }

    // Note that an extension can send data to its webviews using webview.postMessage().
    // This method sends any JSON serializable data to the webview. The message is received
    // inside the webview through the standard message event.
    // The receiving of these messages is done inside webview\index.ts where it
    // calls window.addEventListener('message',...
    // webviewPanel.rpc = new Rpc(m => {
    //   try {
    //     void webviewPanel.webview.postMessage(m)
    //   } catch (e) {
    //     // ignore any disposed object exceptions
    //   }
    // })
    // webviewPanel.rpc.register(this.editorApi)

    // // Similarly, we can received data from the webview by listening to onDidReceiveMessage.
    // webviewPanel.webview.onDidReceiveMessage(m => {
    //   try {
    //     webviewPanel.rpc.messageReceived(m)
    //   } catch {
    //     // ignore any disposed object exceptions
    //   }
    // })
    // webviewPanel.api = webviewPanel.rpc.getApi()
    // webviewPanel.onDidDispose(() => {
    //   this.webviewPanel = undefined
    //   this.clearNotificationHandlers()
    //   this.clearRpcSessions(null) // should be after `webviewPanel = undefined`
    // })
    // this.webviewPanel = webviewPanel
    // webviewPanel.webview.html = this.initialHtml()

    // const uri = editor.document?.uri?.toString()
    // const client = this.clientProvider.findClient(uri)
    await this.initInfoView(editor, this.client!)
    // }
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
      await this.infoviewApi?.serverStopped(undefined) // clear any server stopped state
      await this.infoviewApi?.serverRestarted(client.initializeResult)
      await this.sendDiagnostics(client)
      await this.sendProgress(client)
      await this.sendPosition()
      await this.sendConfig()
    }
  }

  private async sendConfig () {
    await this.infoviewApi?.changedInfoviewConfig({
      allErrorsOnLine: true, //getInfoViewAllErrorsOnLine(),
      autoOpenShowsGoal: true, // getInfoViewAllErrorsOnLine(),
      debounceTime: 50 // getInfoViewAutoOpenShowGoal()
    })
  }

  private async sendDiagnostics (client: LeanClient) {
    if (this.infoviewApi !== undefined) {
      client.getDiagnostics()?.forEach(async (uri, diags) => {
        const params = client.getDiagnosticParams(uri, diags)
        await this.infoviewApi!.gotServerNotification('textDocument/publishDiagnostics', params)
      })
    }
  }

  private async sendProgress (client: LeanClient) {
    if (this.infoviewApi == null) return
    for (const [uri, processing] of client.progress) {
      const params: LeanFileProgressParams = {
        textDocument: {
          uri: c2pConverter.asUri(uri),
          version: 0 // HACK: The infoview ignores this
        },
        processing
      }
      await this.infoviewApi.gotServerNotification('$/lean/fileProgress', params)
    }
  }

  private onLanguageChanged () {
    this.autoOpen().then(async () => {
      await this.sendPosition()
      await this.sendConfig()
    }).catch(() => {})
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
    // if (languages.match(this.leanDocs, editor.document) === 0) {
    //   // language is not yet 'lean4', but the LeanClient will fire the didSetLanguage event
    //   // in openLean4Document and that's when we can send the position to update the
    //   // InfoView for the newly opened document.
    //   return
    // }
    // actual editor
    if (this.clientsFailed.size > 0 || this.workersFailed.size > 0) {
      const client = this.client // this.clientProvider.findClient(editor.document.uri.toString())
      if (client != null) {
        const uri = window.activeTextEditor?.document.uri.toString() ?? ''
        const folder = client.getWorkspaceFolder()
        let reason: any | undefined
        if (this.clientsFailed.has(folder)) {
          reason = this.clientsFailed.get(folder)
        } else if (this.workersFailed.has(uri)) {
          reason = this.workersFailed.get(uri)
        }
        if (reason) {
          // send stopped event
          await this.infoviewApi?.serverStopped(reason)
        } else {
          await this.updateStatus(loc)
        }
      } else {
        console.log('[InfoProvider] ### what does it mean to have sendPosition but no LeanClient for this document???')
      }
    } else {
      await this.updateStatus(loc)
    }
  }

  private async updateStatus (loc: ls.Location | undefined): Promise<void> {
    // await this.infoviewApi?.serverStopped('update status') // clear any server stopped state
    await this.autoOpen()
    await this.infoviewApi?.changedCursorLocation(loc)
  }

  private async revealEditorSelection (uri: Uri, selection?: monaco.Range) {
    if (this.editor == null) {
      console.error("Editor not set")
      return
    }
    if (selection !== undefined) {
      this.editor.revealRange(selection)//TextEditorRevealType.InCenterIfOutsideViewport
      this.editor.setSelection(selection)
      // ensure the text document has the keyboard focus.
      this.editor.focus()
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

  private getLocalPath (path: string): string | undefined {
    // if (this.webviewPanel != null) {
    //   return this.webviewPanel.webview.asWebviewUri(
    //     Uri.file(join(this.context.extensionPath, path))).toString()
    // }
    return undefined
  }
}
