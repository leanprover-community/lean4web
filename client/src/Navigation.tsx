import * as React from 'react'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { IconDefinition } from '@fortawesome/free-solid-svg-icons'

/** A button to appear in the hamburger menu or to navigation bar. */
export const NavButton: React.FC<{
  icon?: IconDefinition
  iconElement?: JSX.Element
  text: string
  onClick?: React.MouseEventHandler<HTMLAnchorElement>
  href?: string
}> = ({icon, iconElement, text, onClick=()=>{}, href=null}) => {
  // note: it seems that we can just leave the `target="_blank"` and it has no
  // effect on links without a `href`. If not, add `if (href)` statement here...
  return <a className="nav-link" onClick={onClick} href={href} target="_blank">
    {iconElement ?? <FontAwesomeIcon icon={icon} />}&nbsp;{text}
  </a>
}

/** A button to appear in the hamburger menu or to navigation bar. */
export const Dropdown: React.FC<{
  open: boolean
  setOpen: React.Dispatch<React.SetStateAction<boolean>>
  icon?: IconDefinition
  text?: string
  useOverlay?: boolean
  onClick?: React.MouseEventHandler<HTMLAnchorElement>
  children?: React.ReactNode
}> = ({open, setOpen, icon, text, useOverlay=false, onClick, children}) => {
  return <><div className='dropdown'>
    <NavButton icon={icon} text={text} onClick={(ev) => {setOpen(!open); onClick(ev); ev.stopPropagation()}} />
    {open &&
      <div className={`dropdown-content${open?'': ' '}`} onClick={() => setOpen(false)}>
        {children}
      </div>
    }
  </div>
    { useOverlay && open &&
     <div className="dropdown-overlay" onClick={(ev) => {setOpen(false); ev.stopPropagation()}}/>
    }
  </>
}

/** A popup which overlays the entire screen. */
export const Popup: React.FC<{
  open: boolean
  handleClose: () => void // TODO: what's the correct type?
  children?: React.ReactNode
}> = ({open, handleClose, children}) => {
  return <div className={`modal-wrapper${open? '': ' hidden'}`}>
    <div className="modal-backdrop" onClick={handleClose} />
      <div className="modal">
        <div className="codicon codicon-close modal-close" onClick={handleClose}></div>
        {children}
      </div>
    </div>
}
