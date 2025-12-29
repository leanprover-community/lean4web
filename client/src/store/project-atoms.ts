import { atom } from 'jotai'

import { urlArgsAtom, urlArgsStableAtom } from './url-atoms'

const DEFAULT_PROJECT = 'MathlibDemo'

/** The currently selected project */
export const projectAtom = atom(
  (get) => {
    const urlArgs = get(urlArgsStableAtom)
    return urlArgs.project ?? DEFAULT_PROJECT
  },
  (get, set, project: string) => {
    const urlArgs = get(urlArgsStableAtom)
    set(urlArgsAtom, { ...urlArgs, project: project !== DEFAULT_PROJECT ? project : undefined })
  },
)
