import * as React from 'react'
import Editor from './Editor'
import './editor/vscode.css'
import './App.css'
import PrivacyPolicy from './PrivacyPolicy'
import { useState } from 'react'

const App: React.FC = () => {
  const [restart, setRestart] = useState()

  return (
    <div className='app'>
      <div className='nav'>
        <span className="nav-link" onClick={restart}>Restart Server</span>
        <PrivacyPolicy />
      </div>
      <Editor setRestart={setRestart}/>
    </div>
  )
}

export default App
