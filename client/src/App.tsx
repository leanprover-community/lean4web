import * as React from 'react'
import './editor/vscode.css'
import './App.css'
import PrivacyPolicy from './PrivacyPolicy'
import { useState, Suspense } from 'react'
const Editor = React.lazy(() => import('./Editor'))


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
        <label htmlFor="file-upload" className="nav-link">
            Load file from disk
        </label>
        <input id="file-upload" type="file" onChange={loadFileFromDisk} />
        <span className="nav-link" onClick={restart}>Restart server</span>
        <PrivacyPolicy />
      </div>
      <Suspense fallback={<div className="loading-ring"></div>}>
        <Editor setRestart={setRestart} setLoad={setLoad} />
      </Suspense>
    </div>
  )
}

export default App
