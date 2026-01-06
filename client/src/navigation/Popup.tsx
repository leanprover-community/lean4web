import { ReactNode } from 'react'

/** A popup which overlays the entire screen. */
export function Popup({
  open,
  handleClose,
  children,
}: {
  open: boolean
  handleClose: () => void // TODO: what's the correct type?
  children?: ReactNode
}) {
  return (
    <div className={`modal-wrapper${open ? '' : ' hidden'}`}>
      <div className="modal-backdrop" onClick={handleClose} />
      <div className="modal">
        <div className="codicon codicon-close modal-close" onClick={handleClose}></div>
        {children}
      </div>
    </div>
  )
}
