import { atom } from 'jotai'
import LZString from 'lz-string'

import { settingsAtom } from '../settings/settings-atoms'
import { freshlyImportedCodeAtom, importedCodeAtom, importUrlAtom } from '../store/import-atoms'
import { urlArgsAtom, urlArgsStableAtom } from '../store/url-atoms'
import { fixedEncodeURIComponent } from '../utils/UrlParsing'

/** Atom which represents the editor content and synchronises it with the url hash. */
export const codeAtom = atom(
  (get) => {
    const urlArgs = get(urlArgsStableAtom)
    if (urlArgs.code) {
      return decodeURIComponent(urlArgs.code)
    }
    if (urlArgs.codez) {
      return LZString.decompressFromBase64(urlArgs.codez)
    }
    return get(freshlyImportedCodeAtom)
  },
  (get, set, code: string) => {
    const urlArgs = get(urlArgsAtom)
    if (code.length == 0) {
      // delete all url arguments if there is no code
      set(urlArgsAtom, { ...urlArgs, url: undefined, code: undefined, codez: undefined })
      return
    }
    if (urlArgs.url) {
      // store freshly imported code and the URL so we can compare later
      const freshlyImportedCode = get(freshlyImportedCodeAtom)
      set(importedCodeAtom, freshlyImportedCode)
      set(importUrlAtom, urlArgs.url)
    } else {
      // if the code matches previously imported code, display the URL instead
      const importedCode = get(importedCodeAtom)
      if (importedCode !== undefined && importedCode === code) {
        const importUrl = get(importUrlAtom)
        set(urlArgsAtom, { ...urlArgs, url: importUrl, code: undefined, codez: undefined })
        return
      }
    }
    const compress = get(settingsAtom).compress
    if (compress) {
      // LZ padds the string with trailing `=`, which mess up the argument parsing
      // and aren't needed for LZ encoding, so we remove them.
      const compressedCode = LZString.compressToBase64(code).replace(/=*$/, '')
      set(urlArgsAtom, { ...urlArgs, url: undefined, code: undefined, codez: compressedCode })
    } else {
      const encodedCode = fixedEncodeURIComponent(code)
      set(urlArgsAtom, { ...urlArgs, url: undefined, code: encodedCode, codez: undefined })
    }
  },
)
