import { ReactNode, useRef } from 'react'
import { FocusTrap } from 'focus-trap-react'
import { useEscape } from '../hooks/useEscape'

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
  const ref = useRef<HTMLDialogElement>(null)

  useEscape(ref, () => {
    handleClose()
  })

  if (!open) return
  return (
    <div className={`modal-wrapper${open ? '' : ' hidden'}`}>
      <div
        className="modal-backdrop"
        aria-hidden={true}
        onClick={handleClose}
      />
      <FocusTrap>
        <dialog ref={ref} className="modal" open={open}>
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
