import { atom } from 'jotai'

/**
 * Atom to store the screen width. Note that this atom needs to be updated with a `useEffect`
 * in `App.tsx`.
 */
export const screenWidthAtom = atom(window?.innerWidth ?? 1024)
