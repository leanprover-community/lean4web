import { useEffect, useRef, useState } from 'react'
import LeanLogo from './assets/logo.svg'
import * as monaco from 'monaco-editor'
import { LeanMonaco, LeanMonacoEditor } from 'lean4monaco'
import settings from './config/settings'
import Split from 'react-split'
import { Menu } from './Navigation'

import './css/App.css'
import './css/Editor.css'

/** Expected arguments which can be provided in the URL. */
interface UrlArgs {
  project: string | null
  url: string | null
  code: string | null
}

/**
 * Format the arguments for displaying in the URL, i.e. join them
 * in the form `#project=Mathlib&url=...`
 */
function formatArgs(args: UrlArgs): string {
  let out = '#' +
    Object.entries(args).filter(([key, val]) => (val !== null && val.trim().length > 0)).map(([key, val]) => (`${key}=${val}`)).join('&')
  if (out == '#') {
    return ' '
  }
  return out
}

/**
 * Parse arguments from URL. These are of the form `#project=Mathlib&url=...`
 */
function parseArgs(): UrlArgs {
  let _args = window.location.hash.replace('#', '').split('&').map((s) => s.split('=')).filter(x => x[0])
  return Object.fromEntries(_args)
}

function App() {
  const codeviewRef = useRef<HTMLDivElement>(null)
  const infoviewRef = useRef<HTMLDivElement>(null)
  const [dragging, setDragging] = useState<boolean | null>(false)

  const [editor, setEditor] = useState<monaco.editor.IStandaloneCodeEditor>()


  /* Option to change themes */
  const isBrowserDefaultDark = () => window.matchMedia('(prefers-color-scheme: dark)').matches
  const [theme, setTheme] = useState(isBrowserDefaultDark() ? 'GithubDark' : 'lightPlus')

  // the data
  const [code, setCode] = useState<string>('')
  const [project, setProject] = useState<string>('mathlib-demo')
  const [url, setUrl] = useState<string|null>(null)
  const [contentFromUrl, setContentFromUrl] = useState<string>('')

  function setContent (code: string) {
    editor?.getModel()?.setValue(code)
    setCode(code)
  }

  // Setting up the editor and infoview
  useEffect(() => {
    const socketUrl = ((window.location.protocol === "https:") ? "wss://" : "ws://") + window.location.host + "/websocket" + "/" + project
    console.log(`socket url: ${socketUrl}`)

    const leanMonaco = new LeanMonaco()
    const leanMonacoEditor = new LeanMonacoEditor()
    ;(async () => {
        await leanMonaco.start({websocket: {url: socketUrl}})
        leanMonaco.setInfoviewElement(infoviewRef.current!)
        await leanMonacoEditor.start(codeviewRef.current!, `/project/${project}.lean`, '')

        setEditor(leanMonacoEditor.editor)

        // Setting hooks for the editor
        leanMonacoEditor.editor.onDidChangeModelContent(() => {
          console.log('content changed')
          setCode(leanMonacoEditor.editor.getModel()?.getValue()!)
        })
    })()
    return () => {
        leanMonacoEditor.dispose()
        leanMonaco.dispose()
    }
  }, [project])

  // Read the URL once
  useEffect(() => {
    if (!editor) { return }
    console.debug('editor is ready')

    // Parse args
    let args = parseArgs()
    console.debug(args)
    if (args.code) {
      let _code = decodeURIComponent(args.code)
      setContent(_code)
    }
    if (args.url) {setUrl(decodeURIComponent(args.url))}
    if (args.project) {
      console.log(`setting project to ${args.project}`)
      setProject(args.project)
    }
  }, [editor])

  // Load content from source URL
  useEffect(() => {
    if (!(editor && url)) { return }
    console.debug(`Loading from ${url}`)
    let txt = "Loading…"
    setContent(txt)
    setContentFromUrl(txt)
    fetch(url)
    .then((response) => response.text())
    .then((code) => {
      setContent(code)
      setContentFromUrl(code)
    })
    .catch( err => {
      let errorTxt = `ERROR: ${err.toString()}`
      setContent(errorTxt)
      setContentFromUrl(errorTxt)
    })
  }, [editor, url])

  // keep url updated on changes
  useEffect(() => {
    if (!editor) { return }
    let _project = (project == 'mathlib-demo' ? null : project)
    if (code === contentFromUrl) {
      if (url !== null) {
        let args = {project: _project, url: encodeURIComponent(url), code: null}
        history.replaceState(undefined, undefined!, formatArgs(args))
      } else {
        let args = {project: _project, url: null, code: null}
        history.replaceState(undefined, undefined!, formatArgs(args))
      }
    } else if (code === "") {
      let args = {project: _project, url: null, code: null}
      history.replaceState(undefined, undefined!, formatArgs(args))
    } else {
      let args = {project: _project, url: null, code: encodeURIComponent(code)}
      history.replaceState(undefined, undefined!, formatArgs(args))
    }
  }, [editor, project, code, contentFromUrl])

  return (
    <div className="app monaco-editor">
      <nav>
        <LeanLogo />
        <Menu
          code={code}
          setContent={setContent}
          project={project}
          setProject={setProject}
          theme={theme}
          setTheme={setTheme}
          setUrl={setUrl}
          contentFromUrl={contentFromUrl}
          settings={settings}/>
      </nav>
      <Split className={`editor ${ dragging? 'dragging':''}`}
        gutter={(index, direction) => {
          const gutter = document.createElement('div')
          gutter.className = `gutter` // no `gutter-${direction}` as it might change
          return gutter
        }}
        gutterStyle={(dimension, gutterSize, index) => {
          return {
            'width': settings.verticalLayout ? '100%' : `${gutterSize}px`,
            'height': settings.verticalLayout ? `${gutterSize}px` : '100%',
            'cursor': settings.verticalLayout ? 'row-resize' : 'col-resize',
            'margin-left': settings.verticalLayout ? 0 : `-${gutterSize}px`,
            'margin-top': settings.verticalLayout ? `-${gutterSize}px` : 0,
            'z-index': 0,
          }}}
        gutterSize={5}
        onDragStart={() => setDragging(true)} onDragEnd={() => setDragging(false)}
        sizes={settings.verticalLayout ? [50, 50] : [70, 30]}
        direction={settings.verticalLayout ? "vertical" : "horizontal"}
        style={{flexDirection: settings.verticalLayout ? "column" : "row"}}>
        <div ref={codeviewRef} className="codeview"
          style={settings.verticalLayout ? {width : '100%'} : {height: '100%'}}></div>
        <div ref={infoviewRef} className="vscode-light infoview"
          style={settings.verticalLayout ? {width : '100%'} : {height: '100%'}}></div>
      </Split>
    </div>
  )
}

export default App
