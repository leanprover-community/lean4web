import { SetStateAction, useAtomValue } from 'jotai'
import { Dispatch } from 'react'

import { isCollaboratingAtom } from '../store/collaboration-atoms'
import { NavButton } from './NavButton'
import RotatingGlobe from './RotatingGlobe'

interface CollaborateButtonProps {
  setJoinCollabOpen: Dispatch<SetStateAction<boolean>>
}

export default function CollaborateButton({
  setJoinCollabOpen,
}: CollaborateButtonProps) {
  const collaborationEnabled = import.meta.env.VITE_COLLAB != 'false'
  const isCollaborating = useAtomValue(isCollaboratingAtom)

  return (
    collaborationEnabled &&
    !isCollaborating && (
      <NavButton
        iconElement={<RotatingGlobe />}
        text="Collaborate"
        onClick={() => {
          setJoinCollabOpen(true)
        }}
      />
    )
  )
}
