import { atom } from 'jotai'

import { CollabStates } from '../api/collab-types'

export const collabRoomAtom = atom('')

export const collabDisplayNameAtom = atom('')

export const collabPasswordAtom = atom<string>()

export const isCollaboratingAtom = atom(false)

export const usersInCollabAtom = atom<CollabStates>()
