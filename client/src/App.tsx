import * as React from 'react'
import { useState, Suspense, useEffect } from 'react'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faArrowRotateRight, faArrowUpRightFromSquare, faDownload, faBars, faXmark, faShield, faHammer, faGear, faStar, faUpload, faCloudArrowUp } from '@fortawesome/free-solid-svg-icons'
import { saveAs } from 'file-saver';

import { Dropdown, NavButton } from './Navigation';
import SettingsPopup from './Popups/Settings'
import PrivacyPopup from './Popups/PrivacyPolicy';
import ToolsPopup from './Popups/Tools';
import LoadUrlPopup from './Popups/LoadUrl';
import LoadZulipPopup from './Popups/LoadZulip';

import lean4webConfig from './config/config'
import settings from './config/settings'

import { ReactComponent as Logo } from './assets/logo.svg'
import { ReactComponent as ZulipIcon } from './assets/zulip.svg'

import './css/App.css'
import './css/Modal.css'
import './css/Navigation.css'

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

const save = (content: string) => {
  var blob = new Blob([content], {type: "text/plain;charset=utf-8"});
  saveAs(blob, "Lean4WebDownload.lean");
}

/** The main application */
const App: React.FC = () => {

  // state for handling the dropdown menus
  const [openNav, setOpenNav] = useState(false)
  const [openExample, setOpenExample] = useState(false)
  const [openLoad, setOpenLoad] = useState(false)

  // state for the popups
  const [privacyOpen, setPrivacyOpen] = useState(false)
  const [toolsOpen, setToolsOpen] = useState(false)
  const [settingsOpen, setSettingsOpen] = useState(false)
  const [loadUrlOpen, setLoadUrlOpen] = useState(false)
  const [loadZulipOpen, setLoadZulipOpen] = useState(false)

  // the restart function is only available once the editor is loaded
  const [restart, setRestart] = useState<(project?) => Promise<void>>()

  /* Option to change themes */
  const isBrowserDefaultDark = () => window.matchMedia('(prefers-color-scheme: dark)').matches
  const [theme, setTheme] = React.useState(isBrowserDefaultDark() ? 'GithubDark' : 'lightPlus')

  // the data
  const [content, setContent] = useState<string>('')
  const [project, setProject] = useState<string>('mathlib-demo')
  const [url, setUrl] = useState<string>(null)
  const [contentFromUrl, setContentFromUrl] = useState<string>(null)

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

  const loadFileFromDisk = (event: React.ChangeEvent<HTMLInputElement>) => {
    const fileToLoad = event.target.files[0]
    var fileReader = new FileReader();
    fileReader.onload = (fileLoadedEvent) => {
        var textFromFileLoaded = fileLoadedEvent.target.result as string;
        setContent(textFromFileLoaded)
    }
    fileReader.readAsText(fileToLoad, "UTF-8")
    setOpenNav(false)
  }

  // keep url updated on changes
  useEffect(() => {
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

  // load content from url
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

  // load different project
  useEffect(() => {
    if (restart) {
      console.log(`changing Lean version to ${project}`)
      restart(project)
    }
  }, [project])

  /** The menu items either appearing inside the dropdown or outside */
  function flexibleMenu (isDropdown = false) { return <>
    <Dropdown open={openExample} setOpen={setOpenExample} icon={faStar} text="Examples"
        onClick={() => {setOpenLoad(false); (!isDropdown && setOpenNav(false))}}>
      {lean4webConfig.projects.map(proj => proj.examples?.map(example =>
        <NavButton
          key={`${proj.name}-${example.name}`}
          icon={faStar} text={example.name}
          onClick={() => {
            loadFromUrl(`${window.location.origin}/examples/${proj.folder}/${example.file}`, proj.folder);
            setOpenExample(false)
          }} />
      ))}
    </Dropdown>
    <Dropdown open={openLoad} setOpen={setOpenLoad} icon={faUpload} text="Load"
        onClick={() => {setOpenExample(false); (!isDropdown && setOpenNav(false))}}>
      <label htmlFor="file-upload" className="nav-link" >
        <FontAwesomeIcon icon={faUpload} /> Load file from disk
      </label>
      <NavButton icon={faCloudArrowUp} text="Load from URL" onClick={() => {setLoadUrlOpen(true)}} />
      <NavButton iconElement={<ZulipIcon />} text="Load Zulip Message" onClick={() => {setLoadZulipOpen(true)}} />
      <input id="file-upload" type="file" onChange={loadFileFromDisk} />
    </Dropdown>
  </>}

  return (
    <div className={'app monaco-editor'}>
      <nav>
        <Logo className='logo' />
        <div className='menu'>
          {!settings.verticalLayout && flexibleMenu(false)}
          <Dropdown open={openNav} setOpen={setOpenNav} icon={openNav ? faXmark : faBars} onClick={() => {setOpenExample(false); setOpenLoad(false)}}>
            {settings.verticalLayout && flexibleMenu(true)}
            <NavButton icon={faGear} text="Settings" onClick={() => {setSettingsOpen(true)}} />
            {restart && <NavButton icon={faArrowRotateRight} text="Restart server" onClick={restart} />}
            <NavButton icon={faHammer} text="Tools: Version" onClick={() => setToolsOpen(true)} />
            <NavButton icon={faDownload} text="Save file" onClick={() => save(content)} />
            <NavButton icon={faShield} text={'Privacy policy'} onClick={() => {setPrivacyOpen(true)}} />
            <NavButton icon={faArrowUpRightFromSquare} text="Lean community" href="https://leanprover-community.github.io/" />
            <NavButton icon={faArrowUpRightFromSquare} text="Lean documentation" href="https://leanprover.github.io/lean4/doc/" />
            <NavButton icon={faArrowUpRightFromSquare} text="GitHub" href="https://github.com/hhu-adam/lean4web" />
          </Dropdown>
          <PrivacyPopup open={privacyOpen} handleClose={() => setPrivacyOpen(false)} />
          <ToolsPopup open={toolsOpen} handleClose={() => setToolsOpen(false)} />
          <LoadUrlPopup open={loadUrlOpen} handleClose={() => setLoadUrlOpen(false)} loadFromUrl={loadFromUrl} />
          <LoadZulipPopup open={loadZulipOpen} handleClose={() => setLoadZulipOpen(false)} setContent={setContent} />
          <SettingsPopup open={settingsOpen} handleClose={() => setSettingsOpen(false)} closeNav={() => setOpenNav(false)}
            theme={theme} setTheme={setTheme} project={project} setProject={setProject} />
        </div>
      </nav>
      <Suspense fallback={<div className="loading-ring"></div>}>
        <Editor setRestart={setRestart}
          value={content} onDidChangeContent={setContent} theme={theme} project={project}/>
      </Suspense>
    </div>
  )
}

export default App
