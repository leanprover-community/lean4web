/*
This file contains the default settings for settings that can be changed by the user.

Note that more Editor options are set in `App.tsx` directly.
*/

// const isBrowserDefaultDark = () => window.matchMedia('(prefers-color-scheme: dark)').matches

type Theme = "Visual Studio Light" | "Visual Studio Dark"

/** Type for the user settings. */
export interface IPreferencesContext {
  /** Lead character to trigger unicode input mode */
  abbreviationCharacter: string
  /** Accept code editors suggestions on Enter */
  acceptSuggestionOnEnter: boolean
  /** Show goal names in Lean infoview box */
  showGoalNames: boolean
  /** Compress the `code=` in the URL into `codez=` using LZ-string */
  compress: boolean,
  /** Display code editor and infoview in narrow, vertically stacked, mobile-friendly mode.
   * Usually inferred from window width. */
  mobile: boolean
  saveInLocalStore: boolean
  /** `light` or `dark` or name of existing theme.
   * Usually inferred from browser dark mode preferences.
   */
  theme: Theme,
  /** Wrap code */
  wordWrap: boolean
}

export const preferenceParams: (keyof IPreferencesContext)[] = [
  "abbreviationCharacter",
  "acceptSuggestionOnEnter",
  // "compress", // not sure if this should be user-settable
  "showGoalNames",
  "mobile",
  "theme",
  "wordWrap",
]

/** The default settings. */
const settings: IPreferencesContext = {
  abbreviationCharacter: '\\',
  acceptSuggestionOnEnter: false,
  showGoalNames: true,
  compress: true,
  /** value likely overwritten with `width < 800` in App.tsx
   * unless provided in URL searchparams or in local storage. */
  mobile: false,
  saveInLocalStore: false, // should be false unless user gave consent.
  theme: 'Visual Studio Light', // irrelevant as it will be overwritten in App.tsx
  wordWrap: true
}

/**
 * For CodeMirror (on mobile only)
 * If you add a Monaco theme, the mobile code-mirror editor will default to its dark theme,
 * unless the theme is in this list.
 */
export const lightThemes: Theme[] = [
  'Visual Studio Light'
]

export default settings
