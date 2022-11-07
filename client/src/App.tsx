import * as React from 'react'
import './editor/vscode.css'
import './App.css'
import PrivacyPolicy from './PrivacyPolicy'
import { useState, Suspense } from 'react'
const Editor = React.lazy(() => import('./Editor'))


const App: React.FC = () => {
  const [restart, setRestart] = useState()

  return (
    <div className='app'>
      <div className='nav'>
        <span className="nav-link" onClick={restart}>Restart Server</span>
        <PrivacyPolicy />
      </div>
      <Suspense fallback={<div className="loading-ring"></div>}>
        <Editor setRestart={setRestart}/>
      </Suspense>
    </div>
  )
}

export default App
