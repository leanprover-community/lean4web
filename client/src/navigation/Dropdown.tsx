import { IconDefinition } from '@fortawesome/free-solid-svg-icons'
import { MouseEventHandler, ReactNode } from 'react'

import { NavButton } from './NavButton'

/** A button to appear in the hamburger menu or to navigation bar. */
export function Dropdown({
  open,
  setOpen,
  icon,
  text,
  useOverlay = false,
  onClick,
  children,
}: {
  open: boolean
  setOpen: (open: boolean) => void
  icon?: IconDefinition
  text?: string
  useOverlay?: boolean
  onClick?: MouseEventHandler<HTMLAnchorElement>
  children?: ReactNode
}) {
  return (
    <>
      <div className="dropdown">
        <NavButton
          icon={icon}
          text={text!}
          onClick={(ev) => {
            setOpen(!open)
            onClick!(ev)
            ev.stopPropagation()
          }}
        />
        {open && (
          <div className={`dropdown-content${open ? '' : ' '}`} onClick={() => setOpen(false)}>
            {children}
          </div>
        )}
      </div>
      {useOverlay && open && (
        <div
          className="dropdown-overlay"
          onClick={(ev) => {
            setOpen(false)
            ev.stopPropagation()
          }}
        />
      )}
    </>
  )
}
