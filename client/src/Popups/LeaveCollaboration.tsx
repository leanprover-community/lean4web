import { useAtom } from 'jotai'
import { FormEvent } from 'react'

import { Popup } from '../navigation/Popup'
import { isCollaboratingAtom } from '../store/collaboration-atoms'

/** The popup to join a collaboration room. */
function LeaveCollaborationPopup({
  open,
  handleClose,
}: {
  open: boolean
  handleClose: () => void
}) {
  const [, setIsCollaborating] = useAtom(isCollaboratingAtom)

  function onSubmit(ev: FormEvent) {
    ev.preventDefault()
    setIsCollaborating(false)
    handleClose()
  }

  return (
    <Popup open={open} handleClose={handleClose}>
      <h2>Leave collaboration?</h2>
      <form onSubmit={onSubmit}>
        <div className="button-row">
          <button
            onClick={(ev) => {
              ev.preventDefault()
              handleClose()
            }}
          >
            Stay
          </button>
          <input type="submit" value="Leave" />
        </div>
      </form>
    </Popup>
  )
}

export default LeaveCollaborationPopup
