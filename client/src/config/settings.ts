/* This file contains the default settings. */

const isBrowserDefaultDark = () => window.matchMedia('(prefers-color-scheme: dark)').matches
  
const settings = {
  'saveInLocalStore': false,
  'inputModeEnabled': true,
  'abbreviationCharacter': '\\',
  'languages': ['lean4', 'lean'],
  'inputModeCustomTranslations': {},
  'eagerReplacementEnabled': true,
  'wordWrap': true,
  'acceptSuggestionOnEnter': false,
  'mobile': false, // value irrelevant as it will be overwritten with `width < 800` in App.tsx
  'theme': 'Visual Studio Light', // irrelevant as it will be overwritten in App.tsx
}

export default settings
