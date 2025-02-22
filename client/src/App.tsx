import { useEffect, useRef, useState } from 'react'
import Split from 'react-split'
import * as monaco from 'monaco-editor'
import CodeMirror, { EditorView } from '@uiw/react-codemirror'
import { LeanMonaco, LeanMonacoEditor, LeanMonacoOptions } from 'lean4monaco'
import LZString from 'lz-string'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faCode } from '@fortawesome/free-solid-svg-icons'

// Local imports
import LeanLogo from './assets/logo.svg'
import defaultSettings, { IPreferencesContext, lightThemes } from './config/settings'
import { Menu } from './Navigation'
import { PreferencesContext } from './Popups/Settings'
import { fixedEncodeURIComponent, formatArgs, lookupUrl, parseArgs } from './utils/UrlParsing'
import { useWindowDimensions } from './utils/WindowWidth'

// CSS
import './css/App.css'
import './css/Editor.css'

/** Returns true if the browser wants dark mode */
function isBrowserDefaultDark() {
  return window.matchMedia('(prefers-color-scheme: dark)').matches
}

function App() {
  const editorRef = useRef<HTMLDivElement>(null)
  const infoviewRef = useRef<HTMLDivElement>(null)
  const [dragging, setDragging] = useState<boolean | null>(false)
  const [editor, setEditor] = useState<monaco.editor.IStandaloneCodeEditor>()
  const [leanMonaco, setLeanMonaco] = useState<LeanMonaco>()
  const [loaded, setLoaded] = useState<boolean>(false)
  const [preferences, setPreferences] = useState<IPreferencesContext>(defaultSettings)
  const { width } = useWindowDimensions()

  // Lean4monaco options
  const [options, setOptions] = useState<LeanMonacoOptions>({
    // placeholder, updated below
    websocket: { url: '' }
  })

  // Because of Monaco's missing mobile support we add a codeMirror editor
  // which can be enabled to do editing.
  // TODO: It would be nice to integrate Lean into CodeMirror better.
  // first step could be to pass the cursor selection to the underlying monaco editor
  const [codeMirror, setCodeMirror] = useState(false)

  // the user data
  const [code, setCode] = useState<string>('')
  const [project, setProject] = useState<string>('mathlib-demo')
  const [url, setUrl] = useState<string | null>(null)
  const [codeFromUrl, setCodeFromUrl] = useState<string>('')

  /** Monaco editor requires the code to be set manually. */
  function setContent (code: string) {
    editor?.getModel()?.setValue(code)
    setCode(code)
  }

  // Load preferences from store in the beginning
  useEffect(() => {
    console.debug('[Lean4web] Preferences: Loading.')

    // only load them once
    if (loaded) { return }

    let saveInLocalStore = false;
    let newPreferences: any = { ...preferences } // TODO: need `any` instead of `IPreferencesContext` here to satisfy ts
    for (const [key, value] of Object.entries(preferences)) {
      let storedValue = window.localStorage.getItem(key)
      if (storedValue) {
        saveInLocalStore = true
        console.debug(`[Lean4web] Found stored value for ${key}: ${storedValue}`)
        if (typeof value === 'string') {
          newPreferences[key] = storedValue
        } else if (typeof value === 'boolean') {
          // Boolean values
          newPreferences[key] = (storedValue === "true")
        } else {
          // other values aren't implemented yet.
          console.error(`[Lean4web] Preferences (key: ${key}) contain a value of unsupported type: ${typeof value}`)
        }
      } else {
        // no stored preferences, set a default value
        if (key == 'theme') {
          if (isBrowserDefaultDark()) {
            console.debug("[Lean4web] Preferences: Set dark theme.")
            newPreferences['theme'] = 'Visual Studio Dark'
          } else {
            console.debug("[Lean4web] Preferences: Set light theme.")
            newPreferences['theme'] = 'Visual Studio Light'
          }
        }
      }
    }
    newPreferences['saveInLocalStore'] = saveInLocalStore
    setPreferences(newPreferences)
    setLoaded(true)
  }, [])

  // Use the window width to switch between mobile/desktop layout
  useEffect(() => {
    // Wait for preferences to be loaded
    if (!loaded) { return }

    const _mobile = width < 800
    if (!preferences.saveInLocalStore && _mobile !== preferences.mobile) {
      setPreferences({ ...preferences, mobile: _mobile })
    }
  }, [width, loaded])

  // Update LeanMonaco options when preferences are loaded or change
  useEffect(() => {
    var socketUrl = ((window.location.protocol === "https:") ? "wss://" : "ws://") +
      window.location.host + "/websocket/" + project
    console.log(`[Lean4web] socket url: ${socketUrl}`)
    var _options: LeanMonacoOptions = {
      websocket: {url: socketUrl},
      // Restrict monaco's extend (e.g. context menu) to the editor itself
      htmlElement: editorRef.current ?? undefined,
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
    setOptions(_options)
  }, [editorRef, project, preferences])

  // Setting up the editor and infoview
  useEffect(() => {
    // Wait for preferences to be loaded
    if (!loaded) { return }
    console.debug('[Lean4web] Restarting Editor!')
    var _leanMonaco = new LeanMonaco()
    var leanMonacoEditor = new LeanMonacoEditor()

    _leanMonaco.setInfoviewElement(infoviewRef.current!)
    ;(async () => {
        await _leanMonaco.start(options)
        await leanMonacoEditor.start(editorRef.current!, `/project/${project}.lean`, code)

        setEditor(leanMonacoEditor.editor)
        setLeanMonaco(_leanMonaco)

        // Add a `Paste` option to the context menu on mobile.
        // Monaco does not support clipboard pasting as all browsers block it
        // due to security reasons. Therefore we use a codeMirror editor overlay
        // which features good mobile support (but no Lean support yet)
        if (preferences.mobile) {
          leanMonacoEditor.editor?.addAction({
            id: "myPaste",
            label: "Paste: open 'Plain Editor' for editing on mobile",
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
        //       console.log(`[Lean4web] Providing definition for: ${word.word}`);
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

        // Keeping the `code` state up-to-date with the changes in the editor
        leanMonacoEditor.editor?.onDidChangeModelContent(() => {
          setCode(leanMonacoEditor.editor?.getModel()?.getValue()!)
        })
    })()
    return () => {
      leanMonacoEditor.dispose()
      _leanMonaco.dispose()
    }
  }, [loaded, project, preferences, options, infoviewRef, editorRef])

  // Read the URL arguments once
  useEffect(() => {
    if (!editor) { return }
    console.debug('[Lean4web] editor is ready')

    // Parse args
    let args = parseArgs()
    if (args.code) {
      let _code = decodeURIComponent(args.code)
      setContent(_code)
    } else if (args.codez) {
      let _code = LZString.decompressFromBase64(args.codez)
      setContent(_code)
    }

    if (args.url) {setUrl(lookupUrl(decodeURIComponent(args.url)))}
    if (args.project && args.project != project) {
      console.log(`[Lean4web] setting project to ${args.project}`)
      setProject(args.project)
    }
  }, [editor])

  // Load content from source URL.
  // Once the editor, this reads the content of any provided `url=` in the URL and
  // saves this content as `contentFromURL`. It is important that we only do this once
  // the editor is loaded, as the `useEffect` below only triggers when the `contentFromURL`
  // changes, otherwise it might overwrite local changes too often.
  useEffect(() => {
    if (!editor || !url) {return}
    console.debug(`[Lean4web] Loading from ${url}`)
    fetch(url)
    .then((response) => response.text())
    .then((code) => {
      setCodeFromUrl(code)
    })
    .catch( err => {
      let errorTxt = `ERROR: ${err.toString()}`
      console.error(errorTxt)
      setCodeFromUrl(errorTxt)
    })
  }, [url, editor])

  // Sets the editors content to the content from the loaded URL.
  // As described above, this requires the editor is loaded, but we do not want to
  // trigger this effect every time the editor is reloaded (e.g. config change) as otherwise
  // we would constantly overwrite the user's local changes
  useEffect(() => {
    if (!codeFromUrl) { return }
    setContent(codeFromUrl)
  }, [codeFromUrl])

  // Keep the URL updated on change
  useEffect(() => {
    if (!editor) { return }

    let _project = (project == 'mathlib-demo' ? null : project)
    let args: {
      project: string | null
      url: string | null
      code: string | null
      codez: string | null
    }
    if (code === "") {
      args = {
        project: _project,
        url: null,
        code: null,
        codez: null
      }
    } else if (url != null && code == codeFromUrl) {
      args = {
        project: _project,
        url: encodeURIComponent(url),
        code: null,
        codez: null
      }
    } else if (preferences.compress) {
      // LZ padds the string with trailing `=`, which mess up the argument parsing
      // and aren't needed for LZ encoding, so we remove them.
      const compressed = LZString.compressToBase64(code).replace(/=*$/, '')
      // // Note: probably temporary; might be worth to always compress as with whitespace encoding
      // // it needs very little for the compressed version to be shorter
      // const encodedCode = fixedEncodeURIComponent(code)
      // console.debug(`[Lean4web]: code length: ${encodedCode.length}, compressed: ${compressed.length}`)
      // if (compressed.length < encodedCode.length) {
        args = {
          project: _project,
          url: null,
          code: null,
          codez: compressed
        }
      // } else {
      //   args = {
      //     project: _project,
      //     url: null,
      //     code: encodedCode,
      //     codez: null
      //   }
      // }
    } else {
      args = {
        project: _project,
        url: null,
        code: fixedEncodeURIComponent(code),
        codez: null
      }
    }
    history.replaceState(undefined, undefined!, formatArgs(args))
  }, [editor, project, code, codeFromUrl])

  return <PreferencesContext.Provider value={{preferences, setPreferences}}>
    <div className="app monaco-editor">
      <nav>
        <LeanLogo />
        <Menu
          code={code}
          setContent={setContent}
          project={project}
          setProject={setProject}
          setUrl={setUrl}
          codeFromUrl={codeFromUrl}
          restart={leanMonaco?.restart}
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
          <div ref={editorRef} className={`codeview${codeMirror ? ' hidden' : ''}`} />
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

}

export default App
