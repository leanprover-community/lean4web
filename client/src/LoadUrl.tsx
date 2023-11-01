import * as React from 'react'
import { faCloudArrowUp, faShield } from '@fortawesome/free-solid-svg-icons';
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome';
import { ReactComponent as ZulipIcon } from './assets/zulip.svg'

export const LoadUrl: React.FC<{loadFromUrl:(url: string) => void}> = ({loadFromUrl}) => {
  const [open, setOpen] = React.useState(false);
  const [error, setError] = React.useState(null);
  const urlRef = React.useRef<HTMLInputElement>();
  const handleOpen = (ev: React.MouseEvent) => {
    setError(null)
    setOpen(true)
    // ev.stopPropagation()
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

  return <>
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
          <input autoFocus type="text" placeholder="Paste URL here" ref={urlRef}/>
          <input type="submit" value="Load"/>
          </form>
        </div>
      </div> : null}
  </>
}


export const LoadZulipMessage: React.FC<{loadZulipMessage:(message: string) => void}> = ({loadZulipMessage}) => {
  const [open, setOpen] = React.useState(false);
  const [error, setError] = React.useState(null);
  const urlRef = React.useRef<HTMLInputElement>();
  const handleOpen = (ev: React.MouseEvent) => {
    setError(null)
    setOpen(true)
    // ev.stopPropagation()
  }
  const handleClose = () => setOpen(false);

  const handleLoad = (ev) => {
    ev.preventDefault()
    let url = urlRef.current.value
    if (!url) {
      setError(`Please enter a URL to a message.`)
      return
    }
    if (!url.startsWith('http://') && !url.startsWith('https://')) {
      url = 'https://' + url
    }
    setError('Feature not implemented yet!')
    // loadZulipMessage(url)
    // setOpen(false)
  }

  return <>
    <span className="nav-link" onClick={handleOpen}>
      <ZulipIcon /> Load Zulip Message
    </span>
    {open?
      <div className="modal-wrapper">
        <div className="modal-backdrop" onClick={handleClose} />
        <div className="modal">
          <div className="codicon codicon-close modal-close" onClick={handleClose}></div>
          <h2>Link to Zulip message</h2>
          <p><i>You get this link from "Share" (mobile) or "Copy link to message" (web). It will
            automatically extract code-blocks wrapped inside <code>```</code>-tags</i>.
          </p>
          {error ? <p className="form-error">{error}</p>: null}
          <form onSubmit={handleLoad}>
          <input autoFocus type="text" placeholder="Link to Zulip message" ref={urlRef}/>
          <input type="submit" value="Parse message"/>
          </form>
        </div>
      </div> : null}
  </>
}
