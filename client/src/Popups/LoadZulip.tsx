import { FormEvent, useRef, useState } from 'react'

import { Popup } from '../navigation/Popup'

function LoadZulipPopup({
  open,
  handleClose,
  setContent,
}: {
  open: boolean
  handleClose: () => void
  setContent: (code: string) => void
}) {
  const [error, setError] = useState('')
  const textInputRef = useRef<HTMLTextAreaElement>(null)

  const handleLoad = (ev: FormEvent) => {
    ev.preventDefault()
    let md = textInputRef.current?.value // TODO: not a URL but text, update the var names

    console.log(`received: ${md}`)

    // regex 1 finds the code-blocks
    let regex1 = /(`{3,})\s*(lean)?\s*\n(.+?)\1/gs
    // regex 2 extracts the code from a codeblock
    let regex2 = /^(`{3,})\s*(?:lean)?\s*\n\s*(.+)\s*\1$/s

    let res = md?.match(regex1)

    if (res) {
      let code =
        res
          .map((s) => {
            return s.match(regex2)![2]
          })
          .join('\n\n-- new codeblock\n\n')
          .trim() + '\n'
      setContent(code)
      //setError('')
      handleClose()
    } else {
      setError('Could not find a code-block in the message')
    }
  }

  return (
    <Popup open={open} handleClose={handleClose}>
      <h2>Link to Zulip message</h2>
      <p>
        Copy paste a zulip message here to extract code-blocks.{' '}
        <i>(mobile: "copy to clipboard", web: "view message source")</i>
      </p>
      {error ? <p className="form-error">{error}</p> : null}
      <form onSubmit={handleLoad}>
        <textarea
          name="Zulip message input"
          autoFocus
          placeholder="Paste Zulip message"
          ref={textInputRef}
        />
        <input type="submit" value="Parse message" />
      </form>
    </Popup>
  )
}

export default LoadZulipPopup
