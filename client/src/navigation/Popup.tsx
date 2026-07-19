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
      <div
        className="modal-backdrop"
        aria-hidden={true}
        onClick={handleClose}
      />
      <div className="modal">
        <button
          className="codicon codicon-close modal-close"
          aria-label="close dialog"
          onClick={handleClose}
        />
        {children}
      </div>
    </div>
  )
}
