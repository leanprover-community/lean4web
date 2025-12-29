import { atom } from 'jotai'
import { selectAtom } from 'jotai/utils'

import { shallowEqual } from '../utils/shallowEqual'
import { locationAtom } from './location-atoms'
import { formatArgs, parseArgs } from './url-converters'
import type { UrlArgs } from './url-types'

/** The parameters which are provided in the url hash, i.e. after the `#`. */
export const urlArgsAtom = atom(
  (get) => {
    const hash = get(locationAtom).hash
    if (hash === undefined) return {} as UrlArgs
    return parseArgs(hash)
  },
  (get, set, val: UrlArgs) => {
    const hash = formatArgs(val)
    const location = get(locationAtom)
    set(locationAtom, { ...location, hash: hash })
  },
)

// Prevent updates unless there is a value change
export const urlArgsStableAtom = selectAtom(urlArgsAtom, (settings) => settings, shallowEqual)
