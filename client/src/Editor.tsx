import * as React from 'react'
import { useEffect, useRef, useState } from 'react'
import './css/Editor.css'
import './editor/infoview.css'
import './editor/vscode.css'
import * as monaco from 'monaco-editor/esm/vs/editor/editor.api.js'
import { loadRenderInfoview } from '@leanprover/infoview/loader'
import { InfoviewApi } from '@leanprover/infoview-api'
import { InfoProvider } from './editor/infoview'
import { LeanClient } from './editor/leanclient'
import { AbbreviationRewriter } from './editor/abbreviation/rewriter/AbbreviationRewriter'
import { AbbreviationProvider } from './editor/abbreviation/AbbreviationProvider'
import { LeanTaskGutter } from './editor/taskgutter'
import Split from 'react-split'
// import Notification from './Notification'
// import { config } from './config/config'
import { IConnectionProvider } from 'monaco-languageclient'
import { toSocket, WebSocketMessageWriter } from 'vscode-ws-jsonrpc'
import { DisposingWebSocketMessageReader } from './reader'
import { monacoSetup } from './monacoSetup'

monacoSetup()

const Editor: React.FC<{onDidChangeContent?, value: string, project: string}> =
    ({onDidChangeContent, value, project}) => {
  const uri = monaco.Uri.parse(`file:///project/${project}.lean`)
  const [editor, setEditor] = useState<monaco.editor.IStandaloneCodeEditor | null>(null)
  const [infoviewApi, setInfoviewApi] = useState<InfoviewApi | null>(null)
  const [infoProvider, setInfoProvider] = useState<InfoProvider | null>(null)
  const codeviewRef = useRef<HTMLDivElement>(null)
  const infoviewRef = useRef<HTMLDivElement>(null)

  useEffect(() => {
    const model = monaco.editor.createModel(value ?? '', 'lean4', uri)
    if (onDidChangeContent) {
      model.onDidChangeContent(() => onDidChangeContent(model.getValue()))
    }
    const editor = monaco.editor.create(codeviewRef.current!, { model, })
    setEditor(editor)
    return () => {
      editor.dispose();
      model.dispose();
    }
  }, [])

  useEffect(() => {
    const socketUrl = ((window.location.protocol === "https:") ? "wss://" : "ws://") + window.location.host + "/websocket" + "/" + project
    console.log(`socket url: ${socketUrl}`)

    const connectionProvider : IConnectionProvider = {
      get: async () => {
        return await new Promise((resolve, reject) => {
          console.log(`connecting ${socketUrl}`)
          const websocket = new WebSocket(socketUrl)
          websocket.addEventListener('open', () => {
            const socket = toSocket(websocket)
            const reader = new DisposingWebSocketMessageReader(socket)
            const writer = new WebSocketMessageWriter(socket)
            resolve({ reader, writer })
          })
        })
      }
    }

    // Following `vscode-lean4/webview/index.ts`
    const client = new LeanClient(connectionProvider, showRestartMessage)
    const infoProvider = new InfoProvider(client)
    const div: HTMLElement = infoviewRef.current!
    const imports = {
      '@leanprover/infoview': `${window.location.origin}/index.production.min.js`,
      'react': `${window.location.origin}/react.production.min.js`,
      'react/jsx-runtime': `${window.location.origin}/react-jsx-runtime.production.min.js`,
      'react-dom': `${window.location.origin}/react-dom.production.min.js`,
      'react-popper': `${window.location.origin}/react-popper.production.min.js`
    }
    loadRenderInfoview(imports, [infoProvider.getApi(), div], setInfoviewApi)
    setInfoProvider(infoProvider)
    client.restart(project)
    return () => {
      infoProvider.dispose();
      client.dispose();
    }
  }, [project])

  const showRestartMessage = () => {
    // setRestartMessage(true)
  }

  useEffect(() => {
    if (infoProvider !== null && editor !== null && infoviewApi !== null) {
      infoProvider.openPreview(editor, infoviewApi)
    }
  }, [editor, infoviewApi, infoProvider])

  return (
    <div className='editor-wrapper'>
      <Split>
        <div ref={codeviewRef} className="codeview"
          style={false ? {width : '100%'} : {height: '100%'}}></div>
        <div ref={infoviewRef} className="vscode-light infoview"
          style={false ? {width : '100%'} : {height: '100%'}}></div>
      </Split>
    </div>
  )
}

export default Editor
