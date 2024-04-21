import * as React from 'react'
import { useEffect, useRef, useState } from 'react'

import * as monaco from 'monaco-editor/esm/vs/editor/editor.api.js'

import { loadRenderInfoview } from '@leanprover/infoview/loader'
import { InfoviewApi } from '@leanprover/infoview-api'
import { InfoProvider } from './infoview'
import { LeanClient } from './client'
import { IConnectionProvider } from 'monaco-languageclient'
import { toSocket, WebSocketMessageWriter } from 'vscode-ws-jsonrpc'

import { WebSocketMessageReader } from 'vscode-ws-jsonrpc';

monaco.languages.register({
  id: 'lean4',
  extensions: ['.lean']
})

const project = 'MathlibLatest'

const code = '#eval 3+1 \n #eval IO.println "hello" \n'

const Editor: React.FC = () => {
  const [editor, setEditor] = useState<monaco.editor.IStandaloneCodeEditor | null>(null)
  const [infoviewApi, setInfoviewApi] = useState<InfoviewApi | null>(null)
  const [infoProvider, setInfoProvider] = useState<InfoProvider | null>(null)
  const infoviewRef = useRef<HTMLDivElement>(null)

  useEffect(() => {
    const model = monaco.editor.createModel(code, 'lean4')
    const editor = monaco.editor.create(document.body, { model, })
    setEditor(editor)

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

    // Following `vscode-lean4/webview/index.ts`
    const client = new LeanClient(connectionProvider)
    const infoProvider = new InfoProvider(client)
    const imports = {
      '@leanprover/infoview': `${window.location.origin}/index.production.min.js`,
      'react': `${window.location.origin}/react.production.min.js`,
      'react/jsx-runtime': `${window.location.origin}/react-jsx-runtime.production.min.js`,
      'react-dom': `${window.location.origin}/react-dom.production.min.js`,
      'react-popper': `${window.location.origin}/react-popper.production.min.js`
    }
    loadRenderInfoview(imports, [infoProvider.getApi(), infoviewRef.current!], (api) => setInfoviewApi(api))
    setInfoProvider(infoProvider)
    client.restart(project)
  }, [])

  useEffect(() => {
    if (infoProvider !== null && editor !== null && infoviewApi !== null) {
      infoProvider.openPreview(editor, infoviewApi)
    }
  }, [editor, infoviewApi, infoProvider])

  return <div ref={infoviewRef} style={{height: '100%'}}></div>
}

export default Editor
