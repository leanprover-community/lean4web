/*
This file contains the default settings for settings that can be changed by the user.

Note that more Editor options are set in `App.tsx` directly.
*/

// const isBrowserDefaultDark = () => window.matchMedia('(prefers-color-scheme: dark)').matches

/** Type for the user settings. */
export interface IPreferencesContext {
  abbreviationCharacter: string
  acceptSuggestionOnEnter: boolean
  compress: boolean, // compress the `code=` in the URL into `codez=` using LZ-string
  mobile: boolean
  saveInLocalStore: boolean
  theme: string,
  wordWrap: boolean
}

/** The default settings. */
const settings: IPreferencesContext = {
  abbreviationCharacter: '\\',
  acceptSuggestionOnEnter: false,
  compress: true,
  mobile: false, // value irrelevant as it will be overwritten with `width < 800` in App.tsx
  saveInLocalStore: false, // should be false unless user gave consent.
  theme: 'Visual Studio Light', // irrelevant as it will be overwritten in App.tsx
  wordWrap: true
}

export default settings
