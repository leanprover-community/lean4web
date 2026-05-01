import { useAtom } from 'jotai'
import { FormEvent, useState } from 'react'

import { Popup } from '../navigation/Popup'
import {
  collabDisplayNameAtom,
  collabPasswordAtom,
  collabRoomAtom,
  isCollaboratingAtom,
} from '../store/collaboration-atoms'

/** The popup to join a collaboration room. */
function CollaborationPopup({ open, handleClose }: { open: boolean; handleClose: () => void }) {
  const [collabRoom, setCollabRoom] = useAtom(collabRoomAtom)
  const [collabDisplayName, setCollabDisplayName] = useAtom(collabDisplayNameAtom)
  const [collabPassword, setCollabPassword] = useAtom(collabPasswordAtom)
  const [, setIsCollaborating] = useAtom(isCollaboratingAtom)
  const [collabError, setCollabError] = useState('')

  function onSubmit(ev: FormEvent) {
    ev.preventDefault()
    const isValid = /^[\w\d]{3,20}$/
    const isValidPwd = /^[\w\d]{1,20}$/
    if (!isValid.test(collabRoom)) {
      setCollabError('Room name must be 3-20 alphanumeric characters.')
      return
    }
    if (collabPassword != undefined && !isValidPwd.test(collabPassword)) {
      setCollabError('The room name must be up to 20 alphanumeric characters.')
      return
    }
    if (!isValid.test(collabDisplayName)) {
      setCollabError('Display name must be 3-20 alphanumeric characters.')
      return
    }
    setCollabError('')
    if (collabRoom) {
      setCollabPassword(undefined)
      setIsCollaborating(true)
      handleClose()
    }
  }

  return (
    <Popup open={open} handleClose={handleClose}>
      <h2>Start or join collaboration</h2>
      <form onSubmit={onSubmit}>
        <div>
          <p>
            Others can join the collaboration by using the same "room name". The "display name" can
            be chosen freely.{' '}
          </p>
          <p>
            An optional password can be provided to restrict room access. Note that supplying a
            different password will not result in an error. Instead each combination of room name
            and password will have its own room.
          </p>
        </div>
        <label>Room name:</label>
        <input
          required
          autoFocus
          type="text"
          placeholder="Room name"
          value={collabRoom}
          onChange={(e) => {
            setCollabRoom(e.target.value)
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
        <label>Password (optional):</label>
        <input
          type="password"
          placeholder="room password"
          value={collabPassword}
          onChange={(e) => {
            const pwd = e.target.value
            if (pwd.length == 0) {
              setCollabPassword(undefined)
            } else {
              setCollabPassword(pwd)
            }
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
