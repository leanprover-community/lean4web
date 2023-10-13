import * as React from 'react'
import { useState, Suspense, useEffect } from 'react'
import './editor/vscode.css'
import './css/App.css'
import './css/dark-theme.css'
import PrivacyPolicy from './PrivacyPolicy'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faUpload, faArrowRotateRight, faArrowUpRightFromSquare, faDownload, faBars, faXmark } from '@fortawesome/free-solid-svg-icons'
const Editor = React.lazy(() => import('./Editor'))
import Logo from "./logo.svg";
import { saveAs } from 'file-saver';
import LoadUrl from './LoadUrl'
import Settings from './Settings'
import Version from './Version'
import Examples from './Examples'
import { useWindowDimensions } from './window_width'
import { config } from './config/config'


const App: React.FC = () => {
  const [restart, setRestart] = useState()

  /* Vertical layout is changeable in the settings.

  If screen width is below 800, default to vertical layout instead. */
  const {width, height} = useWindowDimensions()

  // const [verticalLayout, setVerticalLayout] =
  // React.useState(width < 800)

  // const changeVerticalLayout = () => {
  //   if (verticalLayout) {
  //     setVerticalLayout(false)
  //     // set this to true, so that when switching to vertical layout, the settings stay open
  //     setNavOpen(true)
  //   } else {
  //     setVerticalLayout(true)
  //   }
  // }

  const [navOpen, setNavOpen] = useState(false)

  function closeNav() {
    setNavOpen(false)
  }

  const isBrowserDefaultDark = () => window.matchMedia('(prefers-color-scheme: dark)').matches;
  const [theme, setTheme] = React.useState(isBrowserDefaultDark() ? 'dark' : 'light')

  const [content, setContent] = useState<string>('')
  const [url, setUrl] = useState<string>(null)
  const [contentFromUrl, setContentFromUrl] = useState<string>(null)

  const readHash = () => {
    if (window.location.hash.startsWith('#code=')) {
      setContent(decodeURIComponent(window.location.hash.substring(6)));
    }
    if (window.location.hash.startsWith('#url=')) {
      setUrl(decodeURIComponent(window.location.hash.substring(5)));
    }
  }
  if ("onhashchange" in window) // does the browser support the hashchange event?
    window.addEventListener('hashchange', readHash)

  useEffect(() => { readHash(); }, []) // Trigger onhashchange once in the beginning

  useEffect(() => {
    if (contentFromUrl === content) {
      history.replaceState(undefined, undefined, '#url=' + encodeURIComponent(url));
    } else if (content === "") {
      history.replaceState(undefined, undefined, ' ');
    } else {
      history.replaceState(undefined, undefined, '#code=' + encodeURIComponent(content));
    }
  }, [content])

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

  const onDidChangeContent = (newContent) => {
    setContent(newContent)
  }

  const save = () => {
    var blob = new Blob([content], {type: "text/plain;charset=utf-8"});
    saveAs(blob, "LeanProject.lean");
  }

  const loadFileFromDisk = (event) => {
    const fileToLoad = event.target.files[0]
    var fileReader = new FileReader();
    fileReader.onload = (fileLoadedEvent) => {
        var textFromFileLoaded = fileLoadedEvent.target.result as string;
        setContent(textFromFileLoaded)
    };

    fileReader.readAsText(fileToLoad, "UTF-8");
  }

  const loadFromUrl = (url) => {
    setUrl((oldUrl) => {
      if (oldUrl === url) {
        setContent(contentFromUrl)
      }
      return url
    })
  }

  return (
    <div className={`app ${theme}-theme`}>
      <div className='nav'>
        <Logo className='logo' />
        <div className={'menu dropdown' + (navOpen ? '' : ' hidden')}>
          <Examples loadFromUrl={loadFromUrl} />
          <Settings closeNav={closeNav} theme={theme} setTheme={setTheme}/>
          <span className="nav-link" onClick={restart}>
            <FontAwesomeIcon icon={faArrowRotateRight} /> Restart server
          </span>
          {/* <Version /> */}
          <span className="nav-link" onClick={save}>
            <FontAwesomeIcon icon={faDownload} /> Save file
          </span>
          <label htmlFor="file-upload" className="nav-link">
            <FontAwesomeIcon icon={faUpload} /> Load file from disk
          </label>
          <LoadUrl loadFromUrl={loadFromUrl} />
          <input id="file-upload" type="file" onChange={loadFileFromDisk} />
          <PrivacyPolicy />
          <a className="nav-link" href="https://leanprover-community.github.io/" target="_blank">
            <FontAwesomeIcon icon={faArrowUpRightFromSquare} /> Lean community
          </a>
          <a className="nav-link" href="https://leanprover.github.io/lean4/doc/" target="_blank">
            <FontAwesomeIcon icon={faArrowUpRightFromSquare} /> Lean documentation
          </a>
          <a className="nav-link" href="https://github.com/hhu-adam/lean4web" target="_blank">
            <FontAwesomeIcon icon={faArrowUpRightFromSquare} /> GitHub
          </a>
        </div>
        <div className={"nav-icon"} onClick={(ev) => {setNavOpen(!navOpen)}}>
          {navOpen ? <FontAwesomeIcon icon={faXmark} /> : <FontAwesomeIcon icon={faBars} />}
        </div>
      </div>
      <Suspense fallback={<div className="loading-ring"></div>}>
        <Editor setRestart={setRestart}
          value={content} onDidChangeContent={onDidChangeContent} />
      </Suspense>
    </div>
  )
}

export default App
