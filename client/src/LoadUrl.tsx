import * as React from 'react'
import { faCloudArrowUp, faShield } from '@fortawesome/free-solid-svg-icons';
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome';
import { ReactComponent as ZulipIcon } from './assets/zulip.svg'

export const LoadUrl: React.FC<{loadFromUrl:(url: string) => void, closeNav: any}> = ({loadFromUrl, closeNav}) => {
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
    closeNav()
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


export const LoadZulipMessage: React.FC<{setContent:(message: string) => void, closeNav}> = ({setContent, closeNav}) => {
  const [open, setOpen] = React.useState(false);
  const [error, setError] = React.useState(null);
  const textInputRef = React.useRef<HTMLTextAreaElement>();
  const handleOpen = (ev: React.MouseEvent) => {
    setError(null)
    setOpen(true)
  }
  const handleClose = () => setOpen(false);

  const handleLoad = (ev) => {
    ev.preventDefault()
    let md = textInputRef.current.value // TODO: not a URL but text, update the var names

    console.log(`received: ${md}`)

    // regex 1 finds the code-blocks
    let regex1 = /(`{3,})\s*(lean)?\s*\n(.+?)\1/gs
    // regex 2 extracts the code from a codeblock
    let regex2 = /^(`{3,})\s*(?:lean)?\s*\n\s*(.+)\s*\1$/s

    let res = md.match(regex1)

    if (res) {
      let code = res.map(s => {
        console.log(`match: ${s}`)
        return s.match(regex2)[2]}).join('\n\n-- new codeblock\n\n').trim() + '\n'
      console.log(code)
      setContent(code)
      //setError('')
      setOpen(false)
      closeNav()
    } else {
      setError('Could not find a code-block in the message')
    }
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
          <p>Copy paste a zulip message here to extract
            code-blocks. <i>(mobile: "copy to clipboard",
            web: "view message source")</i>
          </p>
          {error ? <p className="form-error">{error}</p>: null}
          <form onSubmit={handleLoad}>
          <textarea autoFocus placeholder="Paste Zulip message" ref={textInputRef}/>
          <input type="submit" value="Parse message"/>
          </form>
        </div>
      </div> : null}
  </>
}
