import { useAtom } from 'jotai'
import { FormEvent } from 'react'

import { Popup } from '../navigation/Popup'
import { collabRoomAtom, usersInCollabAtom } from '../store/collaboration-atoms'
import { getCollaboratorColor } from '../utils/collabColors'

/** The popup to join a collaboration room. */
function LeaveCollaborationPopup({
  open,
  handleClose,
  handleLeaveCollab,
}: {
  open: boolean
  handleClose: () => void
  handleLeaveCollab: () => void
}) {
  const [collabRoom] = useAtom(collabRoomAtom)
  const [usersInCollab] = useAtom(usersInCollabAtom)

  function onSubmit(ev: FormEvent) {
    ev.preventDefault()
    handleClose()
    handleLeaveCollab()
  }

  return (
    <Popup open={open} handleClose={handleClose}>
      <h2>{`Leave collaboration '${collabRoom}'?`}</h2>
      <form onSubmit={onSubmit}>
        <div className="user-tag-row">
          {Array.from(usersInCollab?.entries() ?? []).map(
            ([clientId, state]) => (
              <div
                className="user-tag"
                key={clientId}
                style={{
                  backgroundColor: `var(${getCollaboratorColor(clientId)})`,
                }}
              >
                {state.user.name}
              </div>
            ),
          )}
        </div>
        <p>When leaving, the current code will be preserved.</p>
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
