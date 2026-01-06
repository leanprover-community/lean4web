// const isBrowserDefaultDark = () => window.matchMedia('(prefers-color-scheme: dark)').matches

export type Theme =
  | 'Visual Studio Light'
  | 'Visual Studio Dark'
  | 'Default High Contrast'
  | 'Cobalt'

export type MobileValues = boolean | 'auto'

/** Type for the settings, including internal ones */
export interface Settings {
  /** Lead character to trigger unicode input mode */
  abbreviationCharacter: string
  /** Accept code editors suggestions on Enter */
  acceptSuggestionOnEnter: boolean
  /** Show goal names in Lean infoview box */
  showGoalNames: boolean
  /** Show expected type in Lean infoview box */
  showExpectedType: boolean
  /** Compress the `code=` in the URL into `codez=` using LZ-string */
  compress: boolean
  /** Display code editor and infoview in narrow, vertically stacked, mobile-friendly mode.
   * Usually inferred from window width. */
  mobile: MobileValues
  /** `light` or `dark` or name of existing theme.
   * Usually inferred from browser dark mode preferences.
   */
  theme: Theme
  /** Wrap code */
  wordWrap: boolean
  // internal: saved to browser storage
  saved: boolean
  // internal: written to search params
  inUrl: boolean
}

/** The settings which are not internal */
export type UserSettings = Omit<Settings, 'saved' | 'inUrl'>

/** Same as `UserSettings` but everything is optional, since single keys might be missing in the browser store */
export type PartialUserSettings = Partial<UserSettings>

/** The default settings. */
export const defaultSettings: UserSettings = {
  abbreviationCharacter: '\\',
  acceptSuggestionOnEnter: false,
  showGoalNames: true,
  showExpectedType: false,
  compress: true,
  mobile: 'auto',
  theme: 'Visual Studio Light', // TODO: introduce "auto" which takes the browser setting.
  wordWrap: true,
}

/**
 * For CodeMirror (on mobile only)
 * If you add a Monaco theme, the mobile code-mirror editor will default to its dark theme,
 * unless the theme is in this list.
 */
export const lightThemes: Theme[] = ['Visual Studio Light']
