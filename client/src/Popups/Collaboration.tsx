import { useAtom } from 'jotai'
import { FormEvent, useState } from 'react'

import { Popup } from '../navigation/Popup'
import {
  collabDisplayNameAtom,
  collabRoomNameAtom,
  isCollaboratingAtom,
} from '../store/collaboration-atoms'

/** The popup to join a collaboration room. */
function CollaborationPopup({ open, handleClose }: { open: boolean; handleClose: () => void }) {
  const [collabRoomName, setCollabRoomName] = useAtom(collabRoomNameAtom)
  const [collabDisplayName, setCollabDisplayName] = useAtom(collabDisplayNameAtom)
  const [, setIsCollaborating] = useAtom(isCollaboratingAtom)
  const [collabError, setCollabError] = useState('')

  function onSubmit(ev: FormEvent) {
    ev.preventDefault()
    const isValid = /^[\w\d]{3,20}$/
    if (!isValid.test(collabRoomName)) {
      setCollabError('Room name must be 3-20 alphanumeric characters.')
      return
    }
    if (!isValid.test(collabDisplayName)) {
      setCollabError('Display name must be 3-20 alphanumeric characters.')
      return
    }
    setCollabError('')
    if (collabRoomName) {
      setIsCollaborating(true)
      handleClose()
    }
  }

  return (
    <Popup open={open} handleClose={handleClose}>
      <h2>Start or join collaboration</h2>
      <form onSubmit={onSubmit}>
        <label>Room name:</label>
        <input
          required
          autoFocus
          type="text"
          placeholder="Room name"
          value={collabRoomName}
          onChange={(e) => {
            setCollabRoomName(e.target.value)
            setCollabError('')
          }}
        />
        <label>Display name:</label>
        <input
          required
          type="text"
          placeholder="Your display name"
          value={collabDisplayName}
          onChange={(e) => {
            setCollabDisplayName(e.target.value)
            setCollabError('')
          }}
        />
        {collabError && <p className="form-error">{collabError}</p>}
        <input type="submit" value="Join" />
      </form>
    </Popup>
  )
}

export default CollaborationPopup
