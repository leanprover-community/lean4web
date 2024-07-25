import { useEffect, useRef, useState } from 'react'
import LeanLogo from './assets/logo.svg'
import * as monaco from 'monaco-editor'
import { LeanMonaco, LeanMonacoEditor } from 'lean4monaco'
import defaultSettings from './config/settings'
import Split from 'react-split'
import { Menu } from './Navigation'
import { IPreferencesContext, PreferencesContext } from './Popups/Settings'
import { useWindowDimensions } from './utils/window_width'
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

  const [preferences, setPreferences] = useState<IPreferencesContext>(defaultSettings)


  /* Option to change themes */
  // const isBrowserDefaultDark = () => window.matchMedia('(prefers-color-scheme: dark)').matches
  // const [theme, setTheme] = useState(isBrowserDefaultDark() ? 'GithubDark' : 'lightPlus')

  // the data
  const [code, setCode] = useState<string>('')
  const [project, setProject] = useState<string>('mathlib-demo')
  const [url, setUrl] = useState<string|null>(null)
  const [contentFromUrl, setContentFromUrl] = useState<string>('')
  const {width, height} = useWindowDimensions()

  function setContent (code: string) {
    editor?.getModel()?.setValue(code)
    setCode(code)
  }

  /** Load preferences from store in the beginning */
  useEffect(() => {
    console.debug('Preferences: Loading.')
    let saveInLocalStore = false;
    let newPreferences: any = { ...preferences } // TODO: need `any` instead of `IPreferencesContext` here to satisfy ts
    for (const [key, value] of Object.entries(preferences)) {
      let storedValue = window.localStorage.getItem(key)
      if (storedValue) {
        saveInLocalStore = true
        console.debug(`Found stored config for ${key}: ${storedValue}`)
        if (typeof value === 'string') {
          newPreferences[key] = storedValue
        } else if (typeof value === 'boolean') {
          // Boolean values
          newPreferences[key] = (storedValue === "true")
        } else {
          // other values aren't implemented yet.
          console.error(`Preferences contain a value of unsupported type: ${typeof value}`)
        }
      }
      newPreferences['saveInLocalStore'] = saveInLocalStore
      setPreferences(newPreferences)
    }
  }, [])

  /** Use the window witdh to switch between mobile/desktop layout */
  useEffect(() => {
    console.debug("Preferences: Set mobile.")
    const _mobile = width < 800
    if (!preferences.saveInLocalStore && _mobile !== preferences.mobile) {
      setPreferences({ ...preferences, mobile: _mobile })
    }
  }, [width])

  // Setting up the editor and infoview
  useEffect(() => {
    const socketUrl = ((window.location.protocol === "https:") ? "wss://" : "ws://") + window.location.host + "/websocket" + "/" + project
    console.log(`socket url: ${socketUrl}`)

    // TODO: is this link still recent?
    // see available options here:
    // https://microsoft.github.io/monaco-editor/typedoc/variables/editor.EditorOptions.html

    const leanMonaco = new LeanMonaco()
    const leanMonacoEditor = new LeanMonacoEditor()
    ;(async () => {
        await leanMonaco.start({websocket: {url: socketUrl}, vscode: {
          // https://microsoft.github.io/monaco-editor/typedoc/variables/editor.EditorOptions.html
          "editor.tabSize": 2,
          // "editor.rulers": [100],
          "editor.lightbulb": {enabled: true},
          "editor.wordWrap": preferences.wordWrap ? "on" : "off",
          "editor.wrappingStrategy": "advanced",
          "editor.semanticHighlighting.enabled": true,
          "editor.acceptSuggestionOnEnter": preferences.acceptSuggestionOnEnter ? "on" : "off", // nope?
          "editor.theme": preferences.theme,
          "editor.eagerReplacementEnabled": true,

          "lean4.input.leader": preferences.abbreviationCharacter
        }})
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
  }, [project, preferences])

  useEffect(() => {
    console.log(`Settings changed`)
    console.log(preferences)
  }, [preferences])
  // Read the URL once
  useEffect(() => {
    if (!editor) { return }
    console.debug('editor is ready')

    // Parse args
    let args = parseArgs()
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
    <PreferencesContext.Provider value={{preferences, setPreferences}}>
      <div className="app monaco-editor">
        <nav>
          <LeanLogo />
          <Menu
            code={code}
            setContent={setContent}
            project={project}
            setProject={setProject}
            setUrl={setUrl}
            contentFromUrl={contentFromUrl} />
        </nav>
        <Split className={`editor ${ dragging? 'dragging':''}`}
          gutter={(index, direction) => {
            const gutter = document.createElement('div')
            gutter.className = `gutter` // no `gutter-${direction}` as it might change
            return gutter
          }}
          gutterStyle={(dimension, gutterSize, index) => {
            return {
              'width': preferences.mobile ? '100%' : `${gutterSize}px`,
              'height': preferences.mobile ? `${gutterSize}px` : '100%',
              'cursor': preferences.mobile ? 'row-resize' : 'col-resize',
              'margin-left': preferences.mobile ? 0 : `-${gutterSize}px`,
              'margin-top': preferences.mobile ? `-${gutterSize}px` : 0,
              'z-index': 0,
            }}}
          gutterSize={5}
          onDragStart={() => setDragging(true)} onDragEnd={() => setDragging(false)}
          sizes={preferences.mobile ? [50, 50] : [70, 30]}
          direction={preferences.mobile ? "vertical" : "horizontal"}
          style={{flexDirection: preferences.mobile ? "column" : "row"}}>
          <div ref={codeviewRef} className="codeview"
            style={preferences.mobile ? {width : '100%'} : {height: '100%'}}></div>
          <div ref={infoviewRef} className="vscode-light infoview"
            style={preferences.mobile ? {width : '100%'} : {height: '100%'}}></div>
        </Split>
      </div>
    </PreferencesContext.Provider>
  )
}

export default App
