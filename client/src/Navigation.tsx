import * as React from 'react'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { IconDefinition } from '@fortawesome/free-solid-svg-icons'

/** A button to appear in the hamburger menu or to navigation bar. */
export const NavButton: React.FC<{
  icon: IconDefinition
  text: string
  onClick?: React.MouseEventHandler<HTMLSpanElement>
  href?: string
}> = ({icon, text, onClick=()=>{}, href=null}) => {
  // note: it seems that we can just leave the `target="_blank"` and it has no
  // effect on links without a `href`. If not, add `if (href)` statement here...
  return <a className="nav-link" onClick={onClick} href={href} target="_blank">
    <FontAwesomeIcon icon={icon} />&nbsp;{text}
  </a>
}

/** A popup which overlays the entire screen. */
export const Popup: React.FC<{
  open: boolean
  handleClose: () => void // TODO: what's the correct type?
  children?: React.ReactNode
}> = ({open, handleClose, children}) => {
  if (open) {
    return <div className="modal-wrapper">
    <div className="modal-backdrop" onClick={handleClose} />
      <div className="modal">
        <div className="codicon codicon-close modal-close" onClick={handleClose}></div>
        {children}
      </div>
    </div>
  } else {
    // don't display closed popup
    return <></>
  }

}
