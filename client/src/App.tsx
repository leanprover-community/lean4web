import * as React from 'react'
import { useState, Suspense, useEffect } from 'react'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faArrowRotateRight, faArrowUpRightFromSquare, faDownload, faBars, faXmark, IconDefinition, faShield, faHammer } from '@fortawesome/free-solid-svg-icons'
import { saveAs } from 'file-saver';

import './css/App.css'
import './css/Modal.css'
import './css/Topbar.css'
import { ReactComponent as Logo } from './assets/logo.svg'

import Examples from './Examples'
import LoadingMenu from './LoadingMenu'
import Settings from './Settings'
import { config } from './config/config'
import { NavButton } from './Navigation';
import { PrivacyPopup, ToolsPopup } from './Popups';

const Editor = React.lazy(() => import('./Editor'))

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

const App: React.FC = () => {
  const [restart, setRestart] = useState<(project?) => Promise<void>>()
  const [navOpen, setNavOpen] = useState(false)
  const menuRef = React.useRef<HTMLDivElement>()
  const submenuRef = React.useRef<HTMLDivElement>()

  const [privacyOpen, setPrivacyOpen] = useState(false)
  const [toolsOpen, setToolsOpen] = useState(false)
  const [settingsOpen, setSettingsOpen] = useState(false)

  // Open a submenu. We manage submenus here so that only one submenu can be open at any time.
  const [submenu, setSubmenu] = useState<React.JSX.Element>(null)

  function openSubmenu(ev: React.MouseEvent, component: React.JSX.Element) {
    setNavOpen(true)
    setSubmenu(component)
    ev.stopPropagation()
  }

  function closeNav() {
    setNavOpen(false)
  }

  /* Option to change themes */
  const isBrowserDefaultDark = () => window.matchMedia('(prefers-color-scheme: dark)').matches
  const [theme, setTheme] = React.useState(isBrowserDefaultDark() ? 'GithubDark' : 'lightPlus')

  const [content, setContent] = useState<string>('')
  const [url, setUrl] = useState<string>(null)
  const [project, setProject] = useState<string>('mathlib-demo')
  const [contentFromUrl, setContentFromUrl] = useState<string>(null)

  const readHash = () => {
    let args = parseArgs()
    if (args.code) {setContent(decodeURIComponent(args.code))}
    if (args.url) {setUrl(decodeURIComponent(args.url))}
    if (args.project) {
      console.log(`setting project to ${args.project}`)
      setProject(args.project)
    }
  }

  const onDidChangeContent = (newContent) => {
    setContent(newContent)
  }

  const save = () => {
    var blob = new Blob([content], {type: "text/plain;charset=utf-8"});
    saveAs(blob, "Lean4WebDownload.lean");
  }

  const loadFromUrl = (url: string, project=null) => {
    setUrl((oldUrl) => {
      if (oldUrl === url) {
        setContent(contentFromUrl)
      }
      return url
    })
    if (project) {
      setProject(project)
    }
  }


  useEffect(() => {
    // Trigger onhashchange once in the beginning
    readHash()

    // Closing the dropdown menu or submenu when clicking outside it.
    // Use `ev.stopPropagation()` or `ev.stopImmediatePropagation()` inside
    // the menu to prevent.
    document.body.addEventListener("click", (ev) => {
      if (menuRef?.current) {
        if (menuRef.current.contains(ev.target as HTMLElement)) {

          if(submenuRef?.current && submenuRef.current.contains(ev.target as HTMLElement)) {
            console.log('keeping submenu open')
          } else {
            // Close submenu when clicking inside the menu
            setSubmenu(null)
            console.log('closing submenu')
          }
          ev.stopImmediatePropagation()
        } else {
          // Close Nav on clicking somewhere outside the menu
          setNavOpen(false)
          console.log('closing nav')
        }
      }
    })
  }, [])


  // // if ("onhashchange" in window) // does the browser support the hashchange event?
  // //   window.addEventListener('hashchange', readHash)

  useEffect(() => {
    //let args = parseArgs()
    let _project = (project == 'mathlib-demo' ? null : project)
    if (content === contentFromUrl) {
      let args = {project: _project, url: encodeURIComponent(url), code: null}
      history.replaceState(undefined, undefined, formatArgs(args))
    } else if (content === "") {
      let args = {project: _project, url: null, code: null}
      history.replaceState(undefined, undefined, formatArgs(args))
    } else {
      let args = {project: _project, url: null, code: encodeURIComponent(content)}
      history.replaceState(undefined, undefined, formatArgs(args))
    }
  }, [project, content])

  useEffect(() => {
    if (url !== null) {
      setContent("Loading...")
      setContentFromUrl("Loading...")
      fetch(url)
      .then((response) => response.text())
      .then((content) => {
        setContent(content)
        setContentFromUrl(content)
      })
      .catch( err => {
        setContent(err.toString())
        setContentFromUrl(err.toString())
      })
    }
  }, [url])

  useEffect(() => {
    if (restart) {
      console.log(`changing Lean version to ${project}`)
      restart(project)
    }
  }, [project])

  return (
    <div className={'app monaco-editor'}>
      <div className='nav'>
        <Logo className='logo' />
        <div className='menu' ref={menuRef}>
          {!config.verticalLayout && <>
            {/* Buttons for desktop version */}
            <Examples loadFromUrl={loadFromUrl} openSubmenu={openSubmenu} closeNav={closeNav}/>
            <LoadingMenu loadFromUrl={loadFromUrl} setContent={setContent} openSubmenu={openSubmenu} closeNav={closeNav}/>
          </>
          }
          <a className={"nav-link nav-icon"} onClick={(ev) => {setNavOpen(!navOpen)}}>
            {navOpen ? <FontAwesomeIcon icon={faXmark} /> : <FontAwesomeIcon icon={faBars} />}
          </a>
          <div className={'dropdown' + (navOpen ? '' : ' hidden')}>
            {config.verticalLayout && <>
              {/* Buttons for mobile version */}
              <Examples loadFromUrl={loadFromUrl} openSubmenu={openSubmenu} closeNav={closeNav}/>
              <LoadingMenu loadFromUrl={loadFromUrl} setContent={setContent} openSubmenu={openSubmenu} closeNav={closeNav}/>
            </>}
            <Settings closeNav={closeNav} theme={theme} setTheme={setTheme}
              project={project} setProject={setProject}/>
            <NavButton icon={faArrowRotateRight} text="Restart server" onClick={restart} />
            <NavButton icon={faHammer} text="Tools: Version" onClick={() => setToolsOpen(true)} />
            <NavButton icon={faDownload} text="Save file" onClick={save} />
            <NavButton icon={faShield} text={'Privacy policy'} onClick={() => {setPrivacyOpen(true)}} />
            <NavButton icon={faArrowUpRightFromSquare} text="Lean community" href="https://leanprover-community.github.io/" />
            <NavButton icon={faArrowUpRightFromSquare} text="Lean documentation" href="https://leanprover.github.io/lean4/doc/" />
            <NavButton icon={faArrowUpRightFromSquare} text="GitHub" href="https://github.com/hhu-adam/lean4web" />
            <div className="submenu" ref={submenuRef}>
              {submenu && submenu}
            </div>
          </div>
        </div>
        <PrivacyPopup open={privacyOpen} handleClose={() => setPrivacyOpen(false)} />
        <ToolsPopup open={toolsOpen} handleClose={() => setToolsOpen(false)} />
      </div>
      <Suspense fallback={<div className="loading-ring"></div>}>
        <Editor setRestart={setRestart}
          value={content} onDidChangeContent={onDidChangeContent} theme={theme} project={project}/>
      </Suspense>
    </div>
  )
}

export default App
