import { faCloudArrowUp, faShield } from '@fortawesome/free-solid-svg-icons';
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome';
import e from 'express';
import * as React from 'react'

const LoadUrl: React.FC<{loadFromUrl:(url: string) => void}> = ({loadFromUrl}) => {
  const [open, setOpen] = React.useState(false);
  const [error, setError] = React.useState(null);
  const urlRef = React.useRef<HTMLInputElement>();
  const handleOpen = () => {
    setError(null)
    setOpen(true)
  }
  const handleClose = () => setOpen(false);

  const handleLoad = (ev) => {
    ev.preventDefault()
    let url = urlRef.current.value
    if (!url) {
      setError(`Please specify a URL.`)
      return
    }
    if (!url.startsWith('http://') && !url.startsWith('https://')) {
      url = 'https://' + url
    }
    loadFromUrl(url)
    setOpen(false)
  }

  return (
    <span>
      <span className="nav-link" onClick={handleOpen}>
        <FontAwesomeIcon icon={faCloudArrowUp} /> Load from URL
      </span>
      {open?
        <div className="modal-wrapper">
          <div className="modal-backdrop" onClick={handleClose} />
          <div className="modal">
            <div className="codicon codicon-close modal-close" onClick={handleClose}></div>
            <h2>Load from URL</h2>
            {error ? <p className="form-error">{error}</p>: null}
            <form onSubmit={handleLoad}>
            <input type="text" placeholder="Paste URL here" ref={urlRef}/>
            <input type="submit" value="Load"/>
            </form>
          </div>
        </div> : null}
    </span>
  )
}

export default LoadUrl
