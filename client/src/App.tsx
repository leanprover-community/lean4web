import { Suspense, useEffect, useRef, useState } from 'react'
import Split from 'react-split'
import * as monaco from 'monaco-editor'
import { LeanMonaco, LeanMonacoEditor, LeanMonacoOptions } from 'lean4monaco'
import defaultSettings, {IPreferencesContext} from './config/settings'
import { Menu } from './Navigation'
import { PreferencesContext } from './Popups/Settings'
import { useWindowDimensions } from './utils/window_width'
import LeanLogo from './assets/logo.svg'
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
    Object.entries(args).filter(([_key, val]) => (val !== null && val.trim().length > 0)).map(([key, val]) => (`${key}=${val}`)).join('&')
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

const isBrowserDefaultDark = () => window.matchMedia('(prefers-color-scheme: dark)').matches

function App() {
  const codeviewRef = useRef<HTMLDivElement>(null)
  const infoviewRef = useRef<HTMLDivElement>(null)
  const [dragging, setDragging] = useState<boolean | null>(false)

  const [editor, setEditor] = useState<monaco.editor.IStandaloneCodeEditor>()

  const [preferences, setPreferences] = useState<IPreferencesContext>(defaultSettings)
  const [loaded, setLoaded] = useState<boolean>(false)

  /* Option to change themes */
  // const isBrowserDefaultDark = () => window.matchMedia('(prefers-color-scheme: dark)').matches
  // const [theme, setTheme] = useState(isBrowserDefaultDark() ? 'GithubDark' : 'lightPlus')

  // the data
  const [code, setCode] = useState<string>('')
  const [project, setProject] = useState<string>('mathlib-demo')
  const [url, setUrl] = useState<string|null>(null)
  const [contentFromUrl, setContentFromUrl] = useState<string>('')
  const { width } = useWindowDimensions()

  function setContent (code: string) {
    editor?.getModel()?.setValue(code)
    setCode(code)
  }

  /** Load preferences from store in the beginning */
  useEffect(() => {
    console.debug('Preferences: Loading.')

    // only load them once
    if (loaded) { return }

    let saveInLocalStore = false;
    let newPreferences: any = { ...preferences } // TODO: need `any` instead of `IPreferencesContext` here to satisfy ts
    for (const [key, value] of Object.entries(preferences)) {
      let storedValue = window.localStorage.getItem(key)
      if (storedValue) {
        saveInLocalStore = true
        console.debug(`Found stored value for ${key}: ${storedValue}`)
        if (typeof value === 'string') {
          newPreferences[key] = storedValue
        } else if (typeof value === 'boolean') {
          // Boolean values
          newPreferences[key] = (storedValue === "true")
        } else {
          // other values aren't implemented yet.
          console.error(`Preferences contain a value of unsupported type: ${typeof value}`)
        }
      } else {
        // no stored preferences
        if (key == 'theme') {
          if (isBrowserDefaultDark()) {
            console.debug("Preferences: Set dark theme.")
            newPreferences['theme'] = 'Visual Studio Dark'
          } else {
            console.debug("Preferences: Set light theme.")
            newPreferences['theme'] = 'Visual Studio Light'
          }
        }
      }
    }
    newPreferences['saveInLocalStore'] = saveInLocalStore
    setPreferences(newPreferences)
    setLoaded(true)
  }, [])

  /** Use the window witdh to switch between mobile/desktop layout */
  useEffect(() => {
    // Wait for preferences to be loaded
    if (!loaded) { return }

    const _mobile = width < 800
    if (!preferences.saveInLocalStore && _mobile !== preferences.mobile) {
      setPreferences({ ...preferences, mobile: _mobile })
    }
  }, [width])

  // Setting up the editor and infoview
  useEffect(() => {
    // Wait for preferences to be loaded
    if (!loaded) { return }

    console.debug('Restarting Editor!')

    const socketUrl = ((window.location.protocol === "https:") ? "wss://" : "ws://") + window.location.host + "/websocket" + "/" + project
    console.log(`socket url: ${socketUrl}`)

    const options: LeanMonacoOptions = {
      websocket: {url: socketUrl},
      vscode: {
        /* To add settings here, you can open your settings in VSCode (Ctrl+,), search
         * for the desired setting, select "Copy Setting as JSON" from the "More Actions"
         * menu next to the selected setting, and paste the copied string here.
         */
        "workbench.colorTheme": preferences.theme,
        "editor.tabSize": 2,
        // "editor.rulers": [100],
        "editor.lightbulb.enabled": "on",
        "editor.wordWrap": preferences.wordWrap ? "on" : "off",
        "editor.wrappingStrategy": "advanced",
        "editor.semanticHighlighting.enabled": true,
        "editor.acceptSuggestionOnEnter": preferences.acceptSuggestionOnEnter ? "on" : "off",
        "lean4.input.eagerReplacementEnabled": true,
        "lean4.input.leader": preferences.abbreviationCharacter
      }
    }

    const leanMonaco = new LeanMonaco()
    const leanMonacoEditor = new LeanMonacoEditor()
    ;(async () => {
        await leanMonaco.start(options)
        leanMonaco.setInfoviewElement(infoviewRef.current!)
        await leanMonacoEditor.start(codeviewRef.current!, `/project/${project}.lean`, '')

        setEditor(leanMonacoEditor.editor)

        // Setting hooks for the editor
        leanMonacoEditor.editor?.onDidChangeModelContent(() => {
          console.log('content changed')
          setCode(leanMonacoEditor.editor?.getModel()?.getValue()!)
        })
    })()
    return () => {
        leanMonacoEditor.dispose()
        leanMonaco.dispose()
    }
  }, [project, preferences])

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
          gutter={(_index, _direction) => {
            const gutter = document.createElement('div')
            gutter.className = `gutter` // no `gutter-${direction}` as it might change
            return gutter
          }}
          gutterStyle={(_dimension, gutterSize, _index) => {
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
