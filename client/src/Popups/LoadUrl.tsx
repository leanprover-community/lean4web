import { useAtom } from 'jotai'
import { FormEvent, useRef, useState } from 'react'

import { Popup } from '../navigation/Popup'
import { setImportUrlAndProjectAtom } from '../store/import-atoms'

function LoadUrlPopup({ open, handleClose }: { open: boolean; handleClose: () => void }) {
  const [, setImportUrlAndProject] = useAtom(setImportUrlAndProjectAtom)
  const [error, setError] = useState('')
  const urlRef = useRef<HTMLInputElement>(null)

  const handleLoad = (ev: FormEvent) => {
    ev.preventDefault()
    let url = urlRef.current?.value
    if (!url) {
      setError(`Please specify a URL.`)
      return
    }
    if (!url.startsWith('http://') && !url.startsWith('https://')) {
      url = 'https://' + url
    }
    setImportUrlAndProject({ url: url })
    handleClose()
  }

  return (
    <Popup open={open} handleClose={handleClose}>
      <h2>Load from URL</h2>
      {error ? <p className="form-error">{error}</p> : null}
      <form onSubmit={handleLoad}>
        <input name="import URL" autoFocus type="text" placeholder="Paste URL here" ref={urlRef} />
        <input type="submit" value="Load" />
      </form>
    </Popup>
  )
}

export default LoadUrlPopup
