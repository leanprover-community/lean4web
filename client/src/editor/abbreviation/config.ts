/* This file is based on `vscode-lean4/vscode-lean4/src/abbreviation/config.ts` */

import { useWindowDimensions } from "../../window_width"

export const config = {
  'inputModeEnabled': true,
  'abbreviationCharacter': '\\',
  'languages': ['lean4', 'lean'],
  'inputModeCustomTranslations': {},
  'eagerReplacementEnabled': true,
  'verticalLayout': false, // value here irrelevant, will be overwritten with `width < 800` in Settings.tsx
  'theme': 'light', // options: light, dark
}
