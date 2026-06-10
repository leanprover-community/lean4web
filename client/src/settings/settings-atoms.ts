import { atomWithStorage, createJSONStorage, selectAtom } from 'jotai/utils'
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

/** "Local Only" settings: always stored on localstorage, never in the URL, always in local storage */
interface PartialLocalOnlyUserSettings {
  /** Hide the navigation bar that otherwise appears when `?from=lean` or `?from=mathlib` is set. */
  hideNavbar?: boolean
}

// Migrate legacy `hideNavBar` option to new setting (added June 2026, delete after October 2026)
if (localStorage.getItem('hideNavBar')) {
  if (localStorage.getItem('hideNavBar') === "true") {
    localStorage.setItem("lean4web:local-settings", '{"hideNavbar":true}')
  }
  localStorage.removeItem('hideNavBar')
}

const localOnlyStorage = createJSONStorage<PartialLocalOnlyUserSettings>(() => localStorage)

/** Delete local storage if all items become falsy */
const prunedLocalOnlyStorage: typeof localOnlyStorage = {
  ...localOnlyStorage,
  setItem(key, value) {
    if (Object.keys(value).length === 0) {
      localOnlyStorage.removeItem(key)
    } else {
      localOnlyStorage.setItem(key, value)
    }
  },
}

const fullLocalOnlySettingsAtom = atomWithStorage<PartialLocalOnlyUserSettings>(
  'lean4web:local-settings',
  {},
  prunedLocalOnlyStorage,
  { getOnInit: true },
)

/** Local-only settings are always stored in local storage, never in the URL */
export const localOnlySettingAtom = atom(
  (get) => get(fullLocalOnlySettingsAtom),
  (get, set, key: keyof PartialLocalOnlyUserSettings, value: boolean) => {
    const next = { ...get(fullLocalOnlySettingsAtom) }
    if (!value) {
      delete next[key]
    } else {
      next[key] = true
    }
    set(fullLocalOnlySettingsAtom, next)
  },
)

/** Static: do the URL's search parameters indicate that we should show a navigation header? */
export const navBarRequestedAtom = atom<null | 'mathlib' | 'lean'>(() => {
  const params = new URLSearchParams(window.location.search)
  const fromParam = params.get('from')
  if (fromParam === 'mathlib') return 'mathlib'
  if (fromParam === 'lean') return 'lean'
  return null
})

/** Which navigation header will be shown */
export const navBarAtom = atom<null | 'mathlib' | 'lean'>((get) => {
  if (get(localOnlySettingAtom).hideNavbar) return null
  return get(navBarRequestedAtom)
})

/** The settings which are set in the searchParams of the opened URL */
const settingsUrlAtom = atom(
  (get) => {
    const searchParams = get(locationAtom).searchParams
    if (!searchParams) return {}
    return decodeSettingsFromURL(searchParams)
  },
  (get, set, val: URLSearchParams) => {
    const location = get(locationAtom)
    set(locationAtom, { ...location, searchParams: val })
  },
)

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
export const settingsAtom = atom(
  (get) => {
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
  },
  (get, set, val: Settings) => {
    const { saved, inUrl, ...settingsToStore } = val

    set(settingsBaseAtom, val)

    if (saved) {
      set(settingsStoreAtom, settingsToStore)
    } else {
      localStorage.removeItem('lean4web:settings')
    }

    const newSearchParams = inUrl ? encodeSettingsToURL(settingsToStore) : new URLSearchParams()
    set(settingsUrlAtom, newSearchParams)
  },
)

/** Indicates whether mobile layout should be used */
export const mobileAtom = atom((get) => {
  const mobile_setting = get(settingsAtom).mobile
  if (mobile_setting === 'auto') {
    const width = get(screenWidthAtom)
    return width < 800
  }
  return mobile_setting
})
