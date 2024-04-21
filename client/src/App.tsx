import * as React from 'react'

const Editor = React.lazy(() => import('./Editor'))

const App: React.FC = () => {

  return (
    <Editor value={'#eval 3+1 \n #eval IO.println "hello" \n'} onDidChangeContent={false} project={'MathlibLatest'}/>
  )
}

export default App
