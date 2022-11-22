import * as React from 'react'
import { useEffect, useRef, useState } from 'react'
import './Editor.css'
import './editor/infoview.css'
import './editor/vscode.css'
import * as monacoLanguageclient from 'monaco-languageclient'
import * as monaco from 'monaco-editor/esm/vs/editor/editor.api.js'
import { renderInfoview } from '@leanprover/infoview'
import { InfoviewApi } from '@leanprover/infoview-api'
import { InfoProvider } from './editor/infoview'
import { LeanClient } from './editor/leanclient'
import languageConfig from 'lean4/language-configuration.json';
import { AbbreviationRewriter } from './editor/abbreviation/rewriter/AbbreviationRewriter'
import { AbbreviationProvider } from './editor/abbreviation/AbbreviationProvider'
import { LeanTaskGutter } from './editor/taskgutter'
import Split from 'react-split'
import Notification from './Notification'
import { loadWASM } from 'onigasm'
import { Registry } from 'monaco-textmate' // peer dependency
import { wireTmGrammars } from 'monaco-editor-textmate'
import * as lightPlusTheme from './lightPlus.json'
import * as leanSyntax from './syntaxes/lean.json'
import * as leanMarkdownSyntax from './syntaxes/lean-markdown.json'
import * as codeblockSyntax from './syntaxes/codeblock.json'

console.log(monacoLanguageclient)

const socketUrl = ((window.location.protocol === "https:") ? "wss://" : "ws://") + window.location.host + "/websocket"

const Editor: React.FC<{setRestart?, onDidChangeContent?, value: string}> =
    ({setRestart, onDidChangeContent, value}) => {
  const uri = monaco.Uri.parse('file:///LeanProject/LeanProject.lean')
  const [editor, setEditor] = useState<monaco.editor.IStandaloneCodeEditor | null>(null)
  // const [editorApi, setEditorApi] = useState<MyEditorApi | null>(null)
  const [infoviewApi, setInfoviewApi] = useState<InfoviewApi | null>(null)
  const [infoProvider, setInfoProvider] = useState<InfoProvider | null>(null)
  const codeviewRef = useRef<HTMLDivElement>(null)
  const infoviewRef = useRef<HTMLDivElement>(null)
  const [dragging, setDragging] = useState<boolean | null>(false)
  const [restartMessage, setRestartMessage] = useState<boolean | null>(false)

  async function liftOff() {

    // map of monaco "language id's" to TextMate scopeNames
    const grammars = new Map()
    grammars.set('lean4', 'source.lean')

    monaco.editor.defineTheme('vs-code-theme-converted', lightPlusTheme as any);

    // register Monaco languages
    monaco.languages.register({
      id: 'lean4',
      extensions: ['.lean']
    })

    monaco.languages.onLanguage('lean4', async () => {
      // The `onLanguage` listener makes sure that the following code is only run once:

      let config: any = languageConfig
      config.autoClosingPairs = config.autoClosingPairs.map(
        pair => { return {'open': pair[0], 'close': pair[1]} }
      )
      monaco.languages.setLanguageConfiguration('lean4', config);

      await loadWASM('./onigasm.wasm')

      const registry = new Registry({
          getGrammarDefinition: async (scopeName) => {
            if (scopeName === 'source.lean') {
              return {
                  format: 'json',
                  content: JSON.stringify(leanSyntax)
              }
            } else if (scopeName === 'source.lean.markdown') {
              return {
                  format: 'json',
                  content: JSON.stringify(leanMarkdownSyntax)
              }
            } else {
              return {
                  format: 'json',
                  content: JSON.stringify(codeblockSyntax)
              }
            }
          }
      })

      await wireTmGrammars(monaco, registry, grammars, editor)
    })

    const model = monaco.editor.getModel(uri) ??
      monaco.editor.createModel(value ?? '', 'lean4', uri)
    if (!model.isAttachedToEditor()) {
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
    }

    // Following `vscode-lean4/webview/index.ts`
    const client = new LeanClient(socketUrl, undefined, uri, showRestartMessage)
    const infoProvider = new InfoProvider(client)
    const div: HTMLElement = infoviewRef.current!
    const infoviewApi = renderInfoview(infoProvider.getApi(), div)
    setInfoProvider(infoProvider)
    setInfoviewApi(infoviewApi)
    client.restart()
  }

  useEffect(() => {
    liftOff()
  }, [])

  const showRestartMessage = () => {
    setRestartMessage(true)
  }

  const restart = async () => {
    await infoProvider.client.stop();
    await infoProvider.client.start();
    infoProvider.openPreview(editor, infoviewApi)
  }

  useEffect(() => {
    if (editor){
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
    if (infoProvider !== null && editor !== null && infoviewApi !== null) {
      console.log('Opening Preview')
      infoProvider.openPreview(editor, infoviewApi)
      const taskgutter = new LeanTaskGutter(infoProvider.client, editor)
    }
    setRestart(() => restart)
  }, [editor, infoviewApi, infoProvider])


  return (
    <div className='editor-wrapper'>
      <Split className={`editor ${ dragging? 'dragging':''}`} gutterSize={5}
        onDragStart={() => setDragging(true)} onDragEnd={() => setDragging(false)}>
        <div ref={codeviewRef} className="codeview"></div>
        <div ref={infoviewRef} className="infoview"></div>
      </Split>
      {restartMessage ?
        <Notification
          restart={() => {setRestartMessage(false); restart()} }
          close={() => {setRestartMessage(false)}} />
        : ''}
    </div>
  )
}

export default Editor
