// const isBrowserDefaultDark = () => window.matchMedia('(prefers-color-scheme: dark)').matches

export type Theme = "Visual Studio Light" | "Visual Studio Dark" | "Default High Contrast" | "Cobalt"

export type MobileValues = boolean | "auto"

/** Type for the settings, including internal ones */
export interface Settings {
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
  mobile: MobileValues
  /** `light` or `dark` or name of existing theme.
   * Usually inferred from browser dark mode preferences.
   */
  theme: Theme,
  /** Wrap code */
  wordWrap: boolean
  // internal: saved to browser storage
  saved: boolean
  // internal: written to search params
  inUrl: boolean
}

/** The settings which are not internal */
export type UserSettings = Omit<Settings, "saved" | "inUrl">

/** Same as `UserSettings` but everything is optional, since single keys might be missing in the browser store */
export type SettingsStore = Partial<UserSettings>

/** The default settings. */
export const defaultSettings: UserSettings = {
  abbreviationCharacter: '\\',
  acceptSuggestionOnEnter: false,
  showGoalNames: true,
  compress: true,
  mobile: "auto",
  theme: 'Visual Studio Light', // irrelevant as it will be overwritten in App.tsx
  wordWrap: true,
}

/**
 * For CodeMirror (on mobile only)
 * If you add a Monaco theme, the mobile code-mirror editor will default to its dark theme,
 * unless the theme is in this list.
 */
export const lightThemes: Theme[] = [
  'Visual Studio Light'
]

export function decodeSettingsFromURL(searchParams: URLSearchParams): SettingsStore {
  return {
      abbreviationCharacter: searchParams.get('abbreviationCharacter') ?? undefined,
      acceptSuggestionOnEnter: parseBooleanSearchParam(searchParams, 'acceptSuggestionOnEnter'),
      mobile: parseBooleanSearchParam(searchParams, 'mobile'),
      compress: parseBooleanSearchParam(searchParams, 'compress'),
      showGoalNames: parseBooleanSearchParam(searchParams, 'showGoalNames'),
      theme: decodeTheme(searchParams.get("theme") ?? undefined),
      wordWrap: parseBooleanSearchParam(searchParams, 'wordWrap'),
    }
}

function decodeTheme(val?: string): Theme | undefined {
  if (val === undefined) return
  switch (val.toLowerCase()) {
    case "light":
      return "Visual Studio Light"
      break
    case "dark":
      return "Visual Studio Dark"
      break
    default:
      console.warn(`expected search param 'theme' to be 'light' or 'dark'.`)
  }
}

function parseBooleanSearchParam(searchParams: URLSearchParams, name: string) {
  const param = searchParams.get(name) ?? undefined
  return convertToBoolean(name,param)
}

/** `name` is only used for the error message */
function convertToBoolean(name: string, val?: string) {
  if (val === undefined) return
  switch (val.toLowerCase()) {
    case "true":
      return true
    case "false":
      return false
    default:
      console.warn(`expected search param '${name}' to be 'true' or 'false'.`)
  }
}

export function encodeSettingsToURL(val: UserSettings): URLSearchParams {
  const searchParams = new URLSearchParams()
  Object.entries(val)
    .filter(([_, v]) => v !== undefined)
    .forEach(([key, v]) => {
      setParam(searchParams, key as keyof UserSettings, v)
    })
  return searchParams
}

function setParam<K extends keyof UserSettings>(searchParams: URLSearchParams, key: K, value: UserSettings[K]) {
  switch (key) {
    case "theme":
      searchParams.set(String(key), lightThemes.includes(value as Theme) ? "light" : "dark")
      break
    case "mobile":
      if (value !== "auto") {
        searchParams.set(String(key), String(value as Boolean))
      }
      break
    default:
      searchParams.set(String(key), String(value))
  }
}
