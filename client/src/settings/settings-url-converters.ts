import {
  lightThemes,
  PartialUserSettings,
  Theme,
  UserSettings,
} from './settings-types'

export function decodeSettingsFromURL(
  searchParams: URLSearchParams,
): PartialUserSettings {
  return {
    abbreviationCharacter:
      searchParams.get('abbreviationCharacter') ?? undefined,
    acceptSuggestionOnEnter: parseBooleanSearchParam(
      searchParams,
      'acceptSuggestionOnEnter',
    ),
    mobile: parseBooleanSearchParam(searchParams, 'mobile'),
    compress: parseBooleanSearchParam(searchParams, 'compress'),
    ruler: parseNumber(searchParams, 'ruler'),
    showGoalNames: parseBooleanSearchParam(searchParams, 'showGoalNames'),
    showExpectedType: parseBooleanSearchParam(searchParams, 'showExpectedType'),
    theme: decodeTheme(searchParams.get('theme') ?? undefined),
    wordWrap: parseBooleanSearchParam(searchParams, 'wordWrap'),
  }
}

function decodeTheme(val?: string): Theme | undefined {
  if (val === undefined) return
  switch (val.toLowerCase()) {
    case 'light':
      return 'Visual Studio Light'
    case 'dark':
      return 'Visual Studio Dark'
    default:
      console.warn(`expected search param 'theme' to be 'light' or 'dark'.`)
  }
}

function parseNumber(searchParams: URLSearchParams, name: string) {
  const param = searchParams.get(name) ?? undefined
  return param ? Number(param) : undefined
}

function parseBooleanSearchParam(searchParams: URLSearchParams, name: string) {
  const param = searchParams.get(name) ?? undefined
  return convertToBoolean(name, param)
}

/** `name` is only used for the error message */
function convertToBoolean(name: string, val?: string) {
  if (val === undefined) return
  switch (val.toLowerCase()) {
    case 'true':
      return true
    case 'false':
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

function setParam<K extends keyof UserSettings>(
  searchParams: URLSearchParams,
  key: K,
  value: UserSettings[K],
) {
  switch (key) {
    case 'theme':
      searchParams.set(
        String(key),
        lightThemes.includes(value as Theme) ? 'light' : 'dark',
      )
      break
    case 'mobile':
      if (value !== 'auto') {
        searchParams.set(String(key), String(value as boolean))
      }
      break
    default:
      searchParams.set(String(key), String(value))
  }
}
