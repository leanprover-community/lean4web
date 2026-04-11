import './css/App.css'
import './css/Editor.css'

import { faCode } from '@fortawesome/free-solid-svg-icons'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import CodeMirror, { EditorView } from '@uiw/react-codemirror'
import { useAtom } from 'jotai/react'
import { LeanMonaco, LeanMonacoEditor, LeanMonacoOptions } from 'lean4monaco'
import * as monaco from 'monaco-editor'
import * as path from 'path'
import { useCallback, useEffect, useRef, useState, useMemo } from 'react'
import Split from 'react-split'
import * as Y from 'yjs'
import { WebrtcProvider } from 'y-webrtc'
import { MonacoBinding } from 'y-monaco'

import LeanLogo from './assets/logo.svg'
import { codeAtom } from './editor/code-atoms'
import { Menu } from './navigation/Navigation'
import { mobileAtom, settingsAtom } from './settings/settings-atoms'
import { lightThemes } from './settings/settings-types'
import { freshlyImportedCodeAtom } from './store/import-atoms'
import { currentProjectAtom } from './store/project-atoms'
import { screenWidthAtom } from './store/window-atoms'
import { save } from './utils/SaveToFile'

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
  const [settings] = useAtom(settingsAtom)
  const [mobile] = useAtom(mobileAtom)
  const [, setScreenWidth] = useAtom(screenWidthAtom)
  const [project] = useAtom(currentProjectAtom)
  const [code, setCode] = useAtom(codeAtom)
  const [freshlyImportedCode] = useAtom(freshlyImportedCodeAtom)
  const ydoc = useMemo(() => new Y.Doc(), [])
  const [provider, setProvider] = useState<WebrtcProvider|null>(null)
  const [binding, setBinding] = useState<MonacoBinding|null>(null)
  const [collabDialogVisible, setCollabDialogVisible] = useState(false)
  const [collabRoomName, setCollabRoomName] = useState('')
  const [collabDisplayName, setCollabDisplayName] = useState('')
  const [isCollaborating, setIsCollaborating] = useState(false)
  const [collabError, setCollabError] = useState('')

  const model = editor?.getModel()

  // Lean4monaco options
  const [options, setOptions] = useState<LeanMonacoOptions>({
    // placeholder, updated below
    websocket: { url: '' },
  })

  // Because of Monaco's missing mobile support we add a codeMirror editor
  // which can be enabled to do editing.
  // TODO: It would be nice to integrate Lean into CodeMirror better.
  // first step could be to pass the cursor selection to the underlying monaco editor
  const [codeMirror, setCodeMirror] = useState(false)

  /** Monaco editor requires the code to be set manually. */
  function setContent(_code: string) {
    editor?.getModel()?.setValue(_code)
    setCode(_code)
  }

  // save the screen width in jotai
  useEffect(() => {
    const handleResize = () => setScreenWidth(window.innerWidth)
    window.addEventListener('resize', handleResize)
    return () => window.removeEventListener('resize', handleResize)
  }, [setScreenWidth])

  // clean up ydoc on unmount
  useEffect(() => {
    return () => ydoc.destroy()
  }, [ydoc])

  // this effect manages the lifetime of the Yjs document and the provider
  useEffect(() => {
    // const provider = new WebsocketProvider('wss://demos.yjs.dev/ws', roomname, ydoc)
    // See https://github.com/yjs/y-webrtc for options
    if (!isCollaborating || !collabRoomName) {
      setProvider(null)
      return
    }

    const signalingUrl = (window.location.protocol === 'https:' ? 'wss://' : 'ws://') + window.location.host.replace(':3000', ':8080') + '/yjs-signaling'
    console.log('COLLAB: Signaling URL:', signalingUrl);

    const provider = new WebrtcProvider(
      collabRoomName, // roomname
      ydoc, 
      { 
        maxConns: 50,
        password: undefined,
        signaling: [signalingUrl],
        filterBcConns: true,
      }
    )
    if (collabDisplayName) {
      provider.awareness.setLocalStateField('user', { name: collabDisplayName })
    }
    setProvider(provider)
    return () => {
      provider?.destroy()
    }
  }, [ydoc, isCollaborating, collabRoomName, collabDisplayName])

  // this effect manages the lifetime of the editor binding
  useEffect(() => {
    if (provider == null || editor == null) {
      return
    }
    console.log('reached', provider)
    const binding = new MonacoBinding(ydoc.getText(), editor.getModel()!, new Set([editor]), provider?.awareness)
    setBinding(binding)
    return () => {
      binding.destroy()
    }
  }, [ydoc, provider, editor])

  // Update LeanMonaco options when preferences are loaded or change
  useEffect(() => {
    if (!project) return

    console.log('[Lean4web] Update lean4monaco options')

    var socketUrl =
      (window.location.protocol === 'https:' ? 'wss://' : 'ws://') +
      window.location.host +
      '/websocket/' +
      project.folder
    console.log(`[Lean4web] Socket url is ${socketUrl}`)
    var _options: LeanMonacoOptions = {
      websocket: { url: socketUrl },
      // Restrict monaco's extend (e.g. context menu) to the editor itself
      htmlElement: editorRef.current ?? undefined,
      vscode: {
        /* To add settings here, you can open your settings in VSCode (Ctrl+,), search
         * for the desired setting, select "Copy Setting as JSON" from the "More Actions"
         * menu next to the selected setting, and paste the copied string here.
         */
        'workbench.colorTheme': settings.theme,
        'editor.tabSize': 2,
        // "editor.rulers": [100],
        'editor.lightbulb.enabled': 'on',
        'editor.wordWrap': settings.wordWrap ? 'on' : 'off',
        'editor.wrappingStrategy': 'advanced',
        'editor.semanticHighlighting.enabled': true,
        'editor.acceptSuggestionOnEnter': settings.acceptSuggestionOnEnter ? 'on' : 'off',
        'lean4.input.eagerReplacementEnabled': true,
        'lean4.infoview.showGoalNames': settings.showGoalNames,
        'lean4.infoview.emphasizeFirstGoal': true,
        'lean4.infoview.showExpectedType': settings.showExpectedType,
        'lean4.infoview.showTooltipOnHover': false,
        'lean4.input.leader': settings.abbreviationCharacter,
      },
    }
    setOptions(_options)
  }, [editorRef, project, settings])

  // Setting up the editor and infoview
  useEffect(() => {
    if (!project) return
    console.debug('[Lean4web] Restarting editor')
    var _leanMonaco = new LeanMonaco()
    var leanMonacoEditor = new LeanMonacoEditor()

    _leanMonaco.setInfoviewElement(infoviewRef.current!)
    ;(async () => {
      await _leanMonaco.start(options)
      await leanMonacoEditor.start(
        editorRef.current!,
        path.join(project.folder, `${project.folder}.lean`),
        code ?? '',
      )

      setEditor(leanMonacoEditor.editor)
      setLeanMonaco(_leanMonaco)

      // Add a `Paste` option to the context menu on mobile.
      // Monaco does not support clipboard pasting as all browsers block it
      // due to security reasons. Therefore we use a codeMirror editor overlay
      // which features good mobile support (but no Lean support yet)
      if (mobile) {
        leanMonacoEditor.editor?.addAction({
          id: 'myPaste',
          label: "Paste: open 'Plain Editor' for editing on mobile",
          // keybindings: [monaco.KeyMod.CtrlCmd | monaco.KeyCode.KEY_V],
          contextMenuGroupId: '9_cutcopypaste',
          run: (_editor) => {
            setCodeMirror(true)
          },
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
            let path = input.resource.path
              .replace(new RegExp('^.*/(?:lean|\.lake/packages/[^/]+/)'), '')
              .replace(new RegExp('\.lean$'), '')

            if (
              window.confirm(
                `Do you want to open the docs?\n\n${path} (line ${input.options.selection.startLineNumber})`,
              )
            ) {
              let newTab = window.open(
                `https://leanprover-community.github.io/mathlib4_docs/${path}.html`,
                '_blank',
              )
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
  }, [infoviewRef, editorRef, options, project, settings])

  /** Set editor content to the code loaded from the URL */
  useEffect(() => {
    if (freshlyImportedCode && model) model.setValue(freshlyImportedCode)
  }, [freshlyImportedCode, model])

  // Disable monaco context menu outside the editor
  useEffect(() => {
    const handleContextMenu = (event: MouseEvent) => {
      const editorContainer = document.querySelector('.editor')
      if (editorContainer && !editorContainer.contains(event.target as Node)) {
        event.stopPropagation()
      }
    }
    document.addEventListener('contextmenu', handleContextMenu, true)
    return () => {
      document.removeEventListener('contextmenu', handleContextMenu, true)
    }
  }, [])

  // Stop the browser's save dialog on Ctrl+S
  const handleKeyDown = useCallback((event: KeyboardEvent) => {
    if ((event.ctrlKey || event.metaKey) && event.key.toLowerCase() === 's') {
      event.preventDefault()
    }
  }, [])

  // Actually save the file on Ctrl+S
  const handleKeyUp = useCallback(
    (event: KeyboardEvent) => {
      if (
        (event.ctrlKey || event.metaKey) &&
        event.key.toLowerCase() === 's' &&
        code !== undefined
      ) {
        event.preventDefault()
        save(code)
      }
    },
    [code],
  )

  useEffect(() => {
    document.addEventListener('keydown', handleKeyDown)
    document.addEventListener('keyup', handleKeyUp)
    return () => {
      document.removeEventListener('keydown', handleKeyDown)
      document.removeEventListener('keyup', handleKeyUp)
    }
  }, [handleKeyDown, handleKeyUp])

  return (
    <div className="app monaco-editor">
      <nav>
        <LeanLogo />
        <Menu
          setContent={setContent}
          restart={leanMonaco?.restart}
          codeMirror={codeMirror}
          setCodeMirror={setCodeMirror}
        />
        <button 
          onClick={() => {
            if (isCollaborating) {
              setIsCollaborating(false)
            } else {
              setCollabDialogVisible(true)
            }
          }}
          style={{ marginLeft: '10px', height: 'fit-content', alignSelf: 'center', padding: '4px 8px', borderRadius: '4px', cursor: 'pointer' }}
        >
          {isCollaborating ? `Collaborating as: ${collabRoomName}/${collabDisplayName}` : 'Collaborate: OFF'}
        </button>
      </nav>
      {collabDialogVisible && (
        <div style={{position: 'fixed', zIndex: 9999, inset: 0, backgroundColor: 'rgba(0,0,0,0.5)', display: 'flex', justifyContent: 'center', alignItems: 'center'}}>
          <form 
            style={{background: 'var(--vscode-editor-background, white)', color: 'var(--vscode-editor-foreground, black)', padding: '20px', borderRadius: '8px', display: 'flex', flexDirection: 'column', gap: '15px', minWidth: '300px', border: '1px solid var(--vscode-dropdown-border, #ccc)'}}
            onSubmit={(e) => {
              e.preventDefault();
              const isValid = /^[a-z0-9]{3,20}$/;
              if (!isValid.test(collabRoomName)) {
                setCollabError("Room name must be 3-20 lowercase alphanumeric characters.");
                return;
              }
              if (!isValid.test(collabDisplayName)) {
                setCollabError("Display name must be 3-20 lowercase alphanumeric characters.");
                return;
              }
              setCollabError("");
              if (collabRoomName) {
                setIsCollaborating(true);
                setCollabDialogVisible(false);
              }
            }}
          >
            <h3 style={{marginTop: 0, marginBottom: 0}}>Join Collaboration</h3>
            {collabError && <div style={{color: 'red', fontSize: '14px'}}>{collabError}</div>}
            <div style={{display: 'flex', flexDirection: 'column', gap: '5px'}}>
              <label>Room Name:</label>
              <input required value={collabRoomName} onChange={e => {setCollabRoomName(e.target.value); setCollabError('');}} style={{padding: '6px', backgroundColor: 'var(--vscode-input-background, white)', color: 'var(--vscode-input-foreground, black)', border: '1px solid var(--vscode-input-border, #ccc)'}} />
            </div>
            <div style={{display: 'flex', flexDirection: 'column', gap: '5px'}}>
              <label>Display Name:</label>
              <input required value={collabDisplayName} onChange={e => {setCollabDisplayName(e.target.value); setCollabError('');}} style={{padding: '6px', backgroundColor: 'var(--vscode-input-background, white)', color: 'var(--vscode-input-foreground, black)', border: '1px solid var(--vscode-input-border, #ccc)'}} />
            </div>
            <div style={{display: 'flex', justifyContent: 'flex-end', gap: '10px', marginTop: '5px'}}>
              <button type="button" onClick={() => {setCollabDialogVisible(false); setCollabError('');}} style={{padding: '6px 12px', cursor: 'pointer'}}>Cancel</button>
              <button type="submit" style={{padding: '6px 12px', cursor: 'pointer'}}>Join</button>
            </div>
          </form>
        </div>
      )}
      <Split
        className={`editor ${dragging ? 'dragging' : ''}`}
        gutter={(_index, _direction) => {
          const gutter = document.createElement('div')
          gutter.className = `gutter` // no `gutter-${direction}` as it might change
          return gutter
        }}
        gutterStyle={(_dimension, gutterSize, _index) => {
          return {
            width: mobile ? '100%' : `${gutterSize}px`,
            height: mobile ? `${gutterSize}px` : '100%',
            cursor: mobile ? 'row-resize' : 'col-resize',
            'margin-left': mobile ? 0 : `-${gutterSize}px`,
            'margin-top': mobile ? `-${gutterSize}px` : 0,
            'z-index': 0,
          }
        }}
        gutterSize={5}
        onDragStart={() => setDragging(true)}
        onDragEnd={() => setDragging(false)}
        sizes={mobile ? [50, 50] : [70, 30]}
        direction={mobile ? 'vertical' : 'horizontal'}
        style={{ flexDirection: mobile ? 'column' : 'row' }}
      >
        <div className="codeview-wrapper" style={mobile ? { width: '100%' } : { height: '100%' }}>
          {codeMirror && (
            <CodeMirror
              className="codeview plain"
              value={code}
              extensions={[EditorView.lineWrapping]}
              height="100%"
              maxHeight="100%"
              theme={lightThemes.includes(settings.theme) ? 'light' : 'dark'}
              onChange={setContent}
            />
          )}
          <div ref={editorRef} className={`codeview${codeMirror ? ' hidden' : ''}`} />
        </div>
        <div
          ref={infoviewRef}
          className="vscode-light infoview"
          style={mobile ? { width: '100%' } : { height: '100%' }}
        >
          <p className={`editor-support-warning${codeMirror ? '' : ' hidden'}`}>
            You are in the plain text editor
            <br />
            <br />
            Go back to the Monaco Editor (click <FontAwesomeIcon icon={faCode} />) for the infoview
            to update!
          </p>
        </div>
      </Split>
    </div>
  )
}

export default App
