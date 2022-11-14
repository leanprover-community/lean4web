import * as React from 'react'
import './editor/vscode.css'
import './App.css'
import PrivacyPolicy from './PrivacyPolicy'
import { useState, Suspense } from 'react'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faUpload, faArrowRotateRight, faArrowUpRightFromSquare } from '@fortawesome/free-solid-svg-icons'
const Editor = React.lazy(() => import('./Editor'))
import Logo from "./logo.svg";

const App: React.FC = () => {
  const [restart, setRestart] = useState()
  const [load, setLoad] = useState<(string) => void >(() => {console.error('not ready to load')})

  const loadFileFromDisk = (event) => {
    const fileToLoad = event.target.files[0]
    var fileReader = new FileReader();
    fileReader.onload = (fileLoadedEvent) => {
        var textFromFileLoaded = fileLoadedEvent.target.result;
        load(textFromFileLoaded)
    };

    fileReader.readAsText(fileToLoad, "UTF-8");
  }

  return (
    <div className='app'>
      <div className='nav'>
        <Logo className='logo' />
        <label htmlFor="file-upload" className="nav-link">
          <FontAwesomeIcon icon={faUpload} /> Load file from disk
        </label>
        <input id="file-upload" type="file" onChange={loadFileFromDisk} />
        <span className="nav-link" onClick={restart}>
          <FontAwesomeIcon icon={faArrowRotateRight} /> Restart server
        </span>
        <PrivacyPolicy />
        <a className="nav-link" href="https://leanprover.github.io/lean4/doc/" target="_blank">
          <FontAwesomeIcon icon={faArrowUpRightFromSquare} /> Lean documentation
        </a>
      </div>
      <Suspense fallback={<div className="loading-ring"></div>}>
        <Editor setRestart={setRestart} setLoad={setLoad} />
      </Suspense>
    </div>
  )
}

export default App
