import * as React from 'react'
import { useEffect, useRef, useState } from 'react'
import './App.css'
import './infoview.css'
import './vscode.css'
import * as monaco from 'monaco-editor/esm/vs/editor/editor.api.js'
import { renderInfoview } from '@leanprover/infoview'
import { InfoviewApi } from '@leanprover/infoview-api'
import { InfoProvider } from './infoview'
import { LeanClient } from './leanclient'

const App: React.FC = () => {
  const uri = monaco.Uri.parse('inmemory://lean4web.lean')
  const [editor, setEditor] = useState<monaco.editor.IStandaloneCodeEditor | null>(null)
  // const [editorApi, setEditorApi] = useState<MyEditorApi | null>(null)
  const [infoviewApi, setInfoviewApi] = useState<InfoviewApi | null>(null)
  const [infoProvider, setInfoProvider] = useState<InfoProvider | null>(null)
  const editorRef = useRef<HTMLDivElement>(null)
  const infoViewRef = useRef<HTMLDivElement>(null)

  useEffect(() => {
    // register Monaco languages
    monaco.languages.register({
      id: 'lean4',
      extensions: ['.lean']
    })

    const model = monaco.editor.getModel(uri) ?? monaco.editor.createModel('#check 0', 'lean4', uri)
    if (!model.isAttachedToEditor()) {
      setEditor(
        monaco.editor.create(editorRef.current!, {
          model,
          glyphMargin: true,
          lightbulb: {
            enabled: true
          },
          automaticLayout: true,
          minimap: {
            enabled: false
          }
        })
      )
    }
  }, [])

  useEffect(() => {
    // Following `vscode-lean4/webview/index.ts`
    const client = new LeanClient(undefined, uri)
    const infoProvider = new InfoProvider(client)
    const div: HTMLElement = infoViewRef.current!
    const infoviewApi = renderInfoview(infoProvider.getApi(), div)
    setInfoProvider(infoProvider)
    setInfoviewApi(infoviewApi)
    client.restart()
  }, [])

  useEffect(() => {
    if (infoProvider !== null && editor !== null && infoviewApi !== null) {
      console.log('Opening Preview')
      infoProvider.openPreview(editor, infoviewApi)
    }
  }, [editor, infoviewApi, infoProvider])

  return (
    <div className="App">
      <div ref={editorRef} className="editor"></div>
      <div ref={infoViewRef} className="infoview"></div>
    </div>
  )
}

export default App
