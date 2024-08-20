import { useEffect, useRef, useState } from 'react'
import Split from 'react-split'
import * as monaco from 'monaco-editor'
import { LeanMonaco, LeanMonacoEditor, LeanMonacoOptions } from 'lean4monaco'
import defaultSettings, {IPreferencesContext} from './config/settings'
import { Menu } from './Navigation'
import { PreferencesContext } from './Popups/Settings'
import { useWindowDimensions } from './utils/window_width'
import LeanLogo from './assets/logo.svg'

import CodeMirror, { EditorView } from '@uiw/react-codemirror'

import './css/App.css'
import './css/Editor.css'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faCode } from '@fortawesome/free-solid-svg-icons'

function fixedEncodeURIComponent(str: string) {
  return encodeURIComponent(str).replace(/[()]/g, function(c) {
    return '%' + c.charCodeAt(0).toString(16);
  })
}

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

// For CodeMirror (on mobile only)
// If you add a Monaco theme, the mobile code-mirror editor will default to its dark theme,
// unless the theme is in this list.
const lightThemes = [
  'Visual Studio Light'
]

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
  const [leanMonaco, setLeanMonaco] = useState<LeanMonaco>()
  const [editor, setEditor] = useState<monaco.editor.IStandaloneCodeEditor>()
  const [preferences, setPreferences] = useState<IPreferencesContext>(defaultSettings)
  const [loaded, setLoaded] = useState<boolean>(false)

  // Because of Monaco's missing mobile support we add a codeMirror editor
  // which can be enabled to do editing.
  // TODO: It would be nice to integrate Lean into CodeMirror better.
  // first step could be to pass the cursor selection to the underlying monaco editor
  const [codeMirror, setCodeMirror] = useState(false)

  /* Option to change themes */
  // const isBrowserDefaultDark = () => window.matchMedia('(prefers-color-scheme: dark)').matches
  // const [theme, setTheme] = useState(isBrowserDefaultDark() ? 'GithubDark' : 'lightPlus')

  // the data
  const [code, setCode] = useState<string>('')
  const [project, setProject] = useState<string>('mathlib-demo')
  const [url, setUrl] = useState<string|null>(null)
  const [contentFromUrl, setContentFromUrl] = useState<string>('')
  const { width } = useWindowDimensions()

  function restart() {
    leanMonaco?.clientProvider?.getClients().map(client => {client.restart()})
  }

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
    console.debug(`width: ${width}`)

    const _mobile = width < 800
    if (!preferences.saveInLocalStore && _mobile !== preferences.mobile) {
      setPreferences({ ...preferences, mobile: _mobile })
    }
  }, [width, loaded])

  // Setting up the editor and infoview
  useEffect(() => {
    // Wait for preferences to be loaded
    if (!loaded) { return }

    console.debug('Restarting Editor!')

    const socketUrl = ((window.location.protocol === "https:") ? "wss://" : "ws://") + window.location.host + "/websocket" + "/" + project
    console.log(`socket url: ${socketUrl}`)

    const options: LeanMonacoOptions = {
      websocket: {url: socketUrl},
      htmlElement: codeviewRef.current!,
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

    var _leanMonaco = new LeanMonaco()
    const leanMonacoEditor = new LeanMonacoEditor()
    ;(async () => {
        await _leanMonaco.start(options)
        _leanMonaco.setInfoviewElement(infoviewRef.current!)
        await leanMonacoEditor.start(codeviewRef.current!, `/project/${project}.lean`, '')

        setEditor(leanMonacoEditor.editor)
        setLeanMonaco(_leanMonaco)

        // Add a `Paste` option to the context menu on mobile.
        // Monaco does not support clipboard pasting as all browsers block it
        // due to security reasons. Therefore we use a codeMirror editor overlay
        // which features good mobile support (but no Lean support yet)
        if (preferences.mobile) {
          leanMonacoEditor.editor.addAction({
            id: "myPaste",
            label: "Paste: open 'Raw Editor' for editing on mobile",
            // keybindings: [monaco.KeyMod.CtrlCmd | monaco.KeyCode.KEY_V],
            contextMenuGroupId: "9_cutcopypaste",
            run: (_editor) => {
              setCodeMirror(true)
            }
          })
        }

        // // TODO: This was an approach to create a new definition provider, but it
        // // wasn't that useful. I'll leave it here in connection with the TODO below for
        // // reference.
        // monaco.languages.registerDefinitionProvider('lean4', {
        //   provideDefinition(model, position) {
        //     const word = model.getWordAtPosition(position);
        //     if (word) {
        //       console.log(`Providing definition for: ${word.word}`);
        //       // Return the location of the definition
        //       return [
        //         {
        //           uri: model.uri,
        //           range: {startLineNumber: 0, startColumn: word.startColumn, endColumn: word.endColumn, endLineNumber: 0}, // Replace with actual definition range
        //         },
        //       ];
        //     }
        //     return null;
        //   },
        // });

        // TODO: Implement Go-To-Definition better
        // This approach only gives us the file on the server (plus line number) it wants
        // to open, is there a better approach?
        const editorService = (leanMonacoEditor.editor as any)?._codeEditorService
        if (editorService) {
          const openEditorBase = editorService.openCodeEditor.bind(editorService)
          editorService.openCodeEditor = async (input: any, source: any) => {
              const result = await openEditorBase(input, source)
              if (result === null) {
                // found this out with `console.debug(input)`:
                // `resource.path` is the file go-to-def tries to open on the disk
                // we try to create a doc-gen link from that. Could not extract the
                // (fully-qualified) decalaration name... with that one could
                // call `...${path}.html#${declaration}`
                let path = input.resource.path.replace(
                  new RegExp("^.*/(?:lean|\.lake/packages/[^/]+/)"), ""
                ).replace(
                  new RegExp("\.lean$"), ""
                )

                if (window.confirm(`Do you want to open the docs?\n\n${path} (line ${input.options.selection.startLineNumber})`)) {
                  let newTab = window.open(`https://leanprover-community.github.io/mathlib4_docs/${path}.html`, "_blank")
                  if (newTab) {
                    newTab.focus()
                  }
                }
              }
              return null
              // return result // always return the base result
          }
        }

        // Setting hooks for the editor
        leanMonacoEditor.editor?.onDidChangeModelContent(() => {
          console.log('content changed')
          setCode(leanMonacoEditor.editor?.getModel()?.getValue()!)
        })
    })()
    return () => {
        leanMonacoEditor.dispose()
        _leanMonaco.dispose()
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
      let args = {project: _project, url: null, code: fixedEncodeURIComponent(code)}
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
            contentFromUrl={contentFromUrl}
            restart={restart}
            codeMirror={codeMirror}
            setCodeMirror={setCodeMirror}
            />
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
          <div className='codeview-wrapper'
            style={preferences.mobile ? {width : '100%'} : {height: '100%'}} >
            { codeMirror &&
              <CodeMirror
                className="codeview plain"
                value={code}
                extensions={[EditorView.lineWrapping]}
                height='100%'
                maxHeight='100%'
                theme={lightThemes.includes(preferences.theme) ? 'light' : 'dark'}
                onChange={setContent} />
            }
            <div ref={codeviewRef} className={`codeview${codeMirror ? ' hidden' : ''}`} />
          </div>
          <div ref={infoviewRef} className="vscode-light infoview"
            style={preferences.mobile ? {width : '100%'} : {height: '100%'}} >
              <p className={`editor-support-warning${codeMirror ? '' : ' hidden'}`} >
                You are in the plain text editor<br /><br />
                Go back to the Monaco Editor (click <FontAwesomeIcon icon={faCode}/>)
                for the infoview to update!
              </p>
          </div>
        </Split>
      </div>

    </PreferencesContext.Provider>
  )
}

export default App
