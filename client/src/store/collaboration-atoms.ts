import { atom } from 'jotai'

export const collabRoomAtom = atom('')

export const collabDisplayNameAtom = atom('')

export const collabPasswordAtom = atom<string>()

export const isCollaboratingAtom = atom(false)
