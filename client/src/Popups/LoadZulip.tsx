import * as React from 'react'
import { Popup } from '../Navigation'

const LoadZulipPopup: React.FC<{
  open: boolean
  handleClose: () => void
  setContent: React.Dispatch<React.SetStateAction<string>>
}> = ({open, handleClose, setContent}) => {

  const [error, setError] = React.useState(null);
  const textInputRef = React.useRef<HTMLTextAreaElement>();

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
      handleClose()
    } else {
      setError('Could not find a code-block in the message')
    }
  }

  return <Popup open={open} handleClose={handleClose}>
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
  </Popup>
}

export default LoadZulipPopup
