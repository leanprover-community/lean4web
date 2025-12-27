import { atomWithStorage, createJSONStorage } from 'jotai/utils'
import { defaultSettings, Settings, SettingsStore } from './settings-types'
import { atom } from 'jotai/vanilla'
import { screenWidthAtom } from '../store/window-atoms'

/** The settings which apply for the current session */
const settingsBaseAtom = atom<Settings>(defaultSettings)

/** User settings as they are stored in storage */
const settingsStoreAtom = atomWithStorage<SettingsStore>('lean4web:settings', undefined, undefined, { getOnInit: true })

/** The user settings  */
export const settingsAtom = atom(get => {
  const base = get(settingsBaseAtom)
  const store = get(settingsStoreAtom)
  return { ...base, ...store } as Settings
})

/** Set the new settings and save the to local storage */
export const applyAndSaveSettingsAtom = atom(null, (get, set, val) => {
  set(settingsBaseAtom, val)
  set(settingsStoreAtom, val)
})

/** Set the new settings without saving to local storage */
export const applySettingsAtom = atom(null, (get, set, val) => {
  set(settingsBaseAtom, val)
  localStorage.removeItem('lean4web:settings')
})

/** Indicates if there are saved settings in storage */
export const hasSettingsSavedAtom = atom(get => {
  const store = get(settingsStoreAtom)
  return store !== undefined
})

/** Indicates whether mobile layout should be used */
export const mobileAtom = atom(
  get => {
    const mobile_setting = get(settingsAtom).mobile
    if (mobile_setting === "auto") {
      const width = get(screenWidthAtom)
      return width < 800
    }
    return mobile_setting
  }
)
