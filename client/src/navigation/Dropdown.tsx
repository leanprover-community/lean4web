import { IconDefinition } from '@fortawesome/free-solid-svg-icons'
import { MouseEventHandler, ReactNode, useRef } from 'react'

import { NavButton } from './NavButton'
import { useEscape } from '../hooks/useEscape'

/** A button to appear in the hamburger menu or the navigation bar. */
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
  onClick?: MouseEventHandler<HTMLElement>
  children?: ReactNode
}) {
  const ref = useRef<HTMLDivElement>(null)

  useEscape(ref, () => {
    setOpen(false)
  })

  return (
    <>
      <div ref={ref} className="dropdown">
        <NavButton
          icon={icon}
          text={text!}
          onClick={(ev) => {
            setOpen(!open)
            onClick!(ev)
            ev.stopPropagation()
          }}
        />
        {open && <div className="dropdown-content">{children}</div>}
      </div>
      {useOverlay && open && (
        <div
          aria-hidden={true}
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
