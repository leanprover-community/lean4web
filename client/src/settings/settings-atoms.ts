import { atomWithStorage, selectAtom } from 'jotai/utils'
import { atom } from 'jotai/vanilla'

import { locationAtom } from '../store/location-atoms'
import { screenWidthAtom } from '../store/window-atoms'
import { cleanObject } from '../utils/cleanObject'
import { shallowEqual } from '../utils/shallowEqual'
import { defaultSettings, PartialUserSettings, Settings } from './settings-types'
import { decodeSettingsFromURL, encodeSettingsToURL } from './settings-url-converters'

/** User settings as they are stored in storage */
const settingsStoreAtom = atomWithStorage<PartialUserSettings>('lean4web:settings', {}, undefined, {
  getOnInit: true,
})

/** The settings which are set in the searchParams of the opened URL */
const settingsUrlAtom = atom<PartialUserSettings>((get) => {
  const searchParams = get(locationAtom).searchParams
  if (!searchParams) return {}
  return decodeSettingsFromURL(searchParams)
})

/** Needed in order for the `settingsAtom` not to update unless the values from the URL actually change */
const settingsUrlStableAtom = selectAtom(settingsUrlAtom, (settings) => settings, shallowEqual)

/** The settings which apply for the current session */
const settingsBaseAtom = atom<Settings>({ saved: false, inUrl: false, ...defaultSettings })

/**
 * The user settings combined from different sources, with decreasing priority:
 * - url params
 * - browser storage
 * - current (local) state (base)
 * - default values (base)
 */
export const settingsAtom = atom((get) => {
  const base = get(settingsBaseAtom)
  const store = cleanObject(get(settingsStoreAtom))
  const url = cleanObject(get(settingsUrlStableAtom))
  return {
    ...base,
    ...store,
    ...url,
    saved: Object.entries(store).length > 0,
    inUrl: Object.entries(url).length > 0,
  } as Settings
})

/** Set the new settings, and write them to browser storage or URL if desired */
export const applySettingsAtom = atom(null, (get, set, val: Settings) => {
  const { saved, inUrl, ...settingsToStore } = val

  set(settingsBaseAtom, val)

  if (saved) {
    set(settingsStoreAtom, settingsToStore)
  } else {
    localStorage.removeItem('lean4web:settings')
  }

  const newSearchParams = inUrl ? encodeSettingsToURL(settingsToStore) : new URLSearchParams()
  const location = get(locationAtom)
  set(locationAtom, { ...location, searchParams: newSearchParams })
})

/** Indicates whether mobile layout should be used */
export const mobileAtom = atom((get) => {
  const mobile_setting = get(settingsAtom).mobile
  if (mobile_setting === 'auto') {
    const width = get(screenWidthAtom)
    return width < 800
  }
  return mobile_setting
})
