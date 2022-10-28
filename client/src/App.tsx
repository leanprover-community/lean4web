import * as React from 'react'
import Editor from './Editor'
import './editor/vscode.css'
import './App.css'
import PrivacyPolicy from './PrivacyPolicy'

const App: React.FC = () => {
  return (
    <div className='app'>
      <div className='nav'>
        <PrivacyPolicy />
      </div>
      <div className='editor-wrapper'>
        <Editor />
      </div>
    </div>
  )
}

export default App
