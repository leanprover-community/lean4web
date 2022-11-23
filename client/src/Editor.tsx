import * as React from 'react'
import { useEffect, useRef, useState } from 'react'
import './Editor.css'
import './editor/infoview.css'
import './editor/vscode.css'
import * as monaco from 'monaco-editor/esm/vs/editor/editor.api.js'
import { renderInfoview } from '@leanprover/infoview'
import { InfoviewApi } from '@leanprover/infoview-api'
import { InfoProvider } from './editor/infoview'
import { AbbreviationRewriter } from './editor/abbreviation/rewriter/AbbreviationRewriter'
import { AbbreviationProvider } from './editor/abbreviation/AbbreviationProvider'
import { LeanTaskGutter } from './editor/taskgutter'
import Split from 'react-split'
import { LeanClient } from './editor/leanclient'

const Editor: React.FC<{onDidChangeContent?, value: string, uri: monaco.Uri, client: LeanClient}> =
    ({onDidChangeContent, value, uri, client}) => {
  const [editor, setEditor] = useState<monaco.editor.IStandaloneCodeEditor | null>(null)
  // const [editorApi, setEditorApi] = useState<MyEditorApi | null>(null)
  const [infoviewApi, setInfoviewApi] = useState<InfoviewApi | null>(null)
  const [infoProvider, setInfoProvider] = useState<InfoProvider | null>(null)
  const codeviewRef = useRef<HTMLDivElement>(null)
  const infoviewRef = useRef<HTMLDivElement>(null)
  const [dragging, setDragging] = useState<boolean | null>(false)

  useEffect(() => {
    if (client === null) return;
    const model = monaco.editor.createModel(value ?? '', 'lean4', uri)
    if (onDidChangeContent) {
      model.onDidChangeContent(() => onDidChangeContent(model.getValue()))
    }
    const editor = monaco.editor.create(codeviewRef.current!, {
      model,
      glyphMargin: true,
      lightbulb: {
        enabled: true
      },
      unicodeHighlight: {
          ambiguousCharacters: false,
      },
      automaticLayout: true,
      minimap: {
        enabled: false
      },
      lineNumbersMinChars: 3,
      'semanticHighlighting.enabled': true,
      theme: 'vs-code-theme-converted'
    })
    setEditor(editor)
    new AbbreviationRewriter(new AbbreviationProvider(), model, editor)

    // Following `vscode-lean4/webview/index.ts`
    const infoProvider = new InfoProvider(client)
    const div: HTMLElement = infoviewRef.current!
    const infoviewApi = renderInfoview(infoProvider.getApi(), div)
    setInfoProvider(infoProvider)
    setInfoviewApi(infoviewApi)
    return () => {model.dispose()}
  }, [client])

  useEffect(() => {
    if (editor && editor.getModel()){
      if (editor.getModel().getValue() != value) {
        editor.pushUndoStop()
        editor.executeEdits("component", [
          { range: editor.getModel().getFullModelRange(), text: value }
        ]);
        editor.setSelection(new monaco.Range(1,1,1,1))
      }
    }
  }, [value])

  useEffect(() => {
    if (client !== null && infoProvider !== null && editor !== null && infoviewApi !== null) {
      infoProvider.openPreview(editor, infoviewApi)
      const taskgutter = new LeanTaskGutter(client, editor)
    }
  }, [client, editor, infoviewApi, infoProvider])


  return (
    <div className='editor-wrapper'>
      <Split className={`editor ${ dragging? 'dragging':''}`} gutterSize={5}
        onDragStart={() => setDragging(true)} onDragEnd={() => setDragging(false)}>
        <div ref={codeviewRef} className="codeview"></div>
        <div ref={infoviewRef} className="infoview"></div>
      </Split>
    </div>
  )
}

export default Editor
