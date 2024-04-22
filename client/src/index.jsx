
import * as monaco from 'monaco-editor/esm/vs/editor/editor.api.js'

import { loadRenderInfoview } from '@leanprover/infoview/loader'

import { EventEmitter } from 'vscode'
import { createConverter } from 'vscode-languageclient/lib/common/codeConverter'
import { toSocket, WebSocketMessageWriter, WebSocketMessageReader } from 'vscode-ws-jsonrpc'

import { MonacoLanguageClient } from 'monaco-languageclient'

const diagnosticsEmitter = new EventEmitter()

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

const code = '#eval 3+1 \n #eval IO.println "hello" \n'

monaco.languages.register({ id: 'lean4', extensions: ['.lean'] })

const model = monaco.editor.createModel(code, 'lean4')
const editor = monaco.editor.create(document.body, { model, })

const client = new MonacoLanguageClient({ id: 'lean4', name: 'Lean 4', clientOptions, connectionProvider })

let infoviewApi = null

class InfoProvider {

  editorApi = {
    createRpcSession: async (uri) => {
      const result = await client.sendRequest('$/lean/rpc/connect', { uri })
      return result.sessionId
    },
    sendClientRequest: async (_uri, method, params) => {
      return await client.sendRequest(method, params)
    },
    subscribeServerNotifications: async (method) => {

      if (method === 'textDocument/publishDiagnostics') {
        diagnosticsEmitter.event((params) => infoviewApi.gotServerNotification(method, params))
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

  async initInfoView (uri) {
    
    const range = { start: { line: 0, character: 0 }, end: { line: 0, character: 0 } }
    await infoviewApi.initialize({ uri, range })
    await infoviewApi.serverRestarted(client.initializeResult)
  }

}

const infoProvider = new InfoProvider()
const imports = {
  '@leanprover/infoview': `${window.location.origin}/index.production.min.js`,
  'react': `${window.location.origin}/react.production.min.js`,
  'react/jsx-runtime': `${window.location.origin}/react-jsx-runtime.production.min.js`,
  'react-dom': `${window.location.origin}/react-dom.production.min.js`,
  'react-popper': `${window.location.origin}/react-popper.production.min.js`
}

loadRenderInfoview(imports, [infoProvider.editorApi, document.body], async (api) => {
  
  infoviewApi = api
  
  await client.start()

  const uri = editor.getModel().uri.toString()
  infoProvider.initInfoView(uri)
})
