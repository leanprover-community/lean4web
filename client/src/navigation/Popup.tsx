import { ReactNode, useEffect } from 'react'
import { FocusTrap } from 'focus-trap-react'

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
  useEffect(() => {
    if (!open) return
    const handleKeyDown = (ev: KeyboardEvent) => {
      if (ev.key === 'Escape') {
        ev.preventDefault()
        handleClose()
      }
    }
    document.addEventListener('keydown', handleKeyDown)
    return () => {
      document.removeEventListener('keydown', handleKeyDown)
    }
  }, [open, handleClose])

  if (!open) return
  return (
    <div className={`modal-wrapper${open ? '' : ' hidden'}`}>
      <div
        className="modal-backdrop"
        aria-hidden={true}
        onClick={handleClose}
      />
      <FocusTrap>
        <dialog className="modal" open={open}>
          <button
            className="codicon codicon-close modal-close"
            aria-label="close dialog"
            onClick={handleClose}
          />
          {children}
        </dialog>
      </FocusTrap>
    </div>
  )
}
