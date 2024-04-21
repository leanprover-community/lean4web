import * as React from 'react'
import { useEffect, useRef, useState } from 'react'

import * as monaco from 'monaco-editor/esm/vs/editor/editor.api.js'

import { loadRenderInfoview } from '@leanprover/infoview/loader'
import { InfoviewApi } from '@leanprover/infoview-api'
import { InfoProvider, LeanClient } from './infoview'

const code = '#eval 3+1 \n #eval IO.println "hello" \n'

const Editor: React.FC = () => {
  
  const infoviewRef = useRef<HTMLDivElement>(null)

  const [infoviewApi, setInfoviewApi] = useState<InfoviewApi | null>(null)
  const [infoProvider, setInfoProvider] = useState<InfoProvider | null>(null)

  useEffect(() => {

    monaco.languages.register({ id: 'lean4', extensions: ['.lean'] })

    const model = monaco.editor.createModel(code, 'lean4')
    const editor = monaco.editor.create(document.body, { model, })

    const client = new LeanClient()
    const infoProvider = new InfoProvider(client, editor)
    const imports = {
      '@leanprover/infoview': `${window.location.origin}/index.production.min.js`,
      'react': `${window.location.origin}/react.production.min.js`,
      'react/jsx-runtime': `${window.location.origin}/react-jsx-runtime.production.min.js`,
      'react-dom': `${window.location.origin}/react-dom.production.min.js`,
      'react-popper': `${window.location.origin}/react-popper.production.min.js`
    }
    loadRenderInfoview(imports, [infoProvider.editorApi, infoviewRef.current!], (api) => {
      setInfoviewApi(api)
      setInfoProvider(infoProvider)
    })
    client.start()
  }, [])

  useEffect(() => {
    if (infoProvider !== null && infoviewApi !== null) {
      infoProvider.setInfoviewApi(infoviewApi)
      infoProvider.initInfoView()
    }
  }, [infoviewApi, infoProvider])

  return <div ref={infoviewRef}></div>
}

export default Editor
