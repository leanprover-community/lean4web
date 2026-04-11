import { atom } from 'jotai'
import LZString from 'lz-string'

import { settingsAtom } from '../settings/settings-atoms'
import { importedCodeAtom, importUrlAtom, importUrlBaseAtom } from '../store/import-atoms'
import { urlArgsAtom, urlArgsStableAtom } from '../store/url-atoms'
import { fixedEncodeURIComponent } from '../utils/UrlParsing'

/** Atom which represents the editor content and synchronises it with the url hash. */
export const codeAtom = atom(
  (get) => {
    const urlArgs = get(urlArgsStableAtom)
    if (urlArgs.url) {
      return get(importedCodeAtom)
    } else if (urlArgs.code) {
      return urlArgs.code
    }
    if (urlArgs.codez) {
      return LZString.decompressFromBase64(urlArgs.codez)
    } else {
      return ''
    }
  },
  (get, set, code: string) => {
    const urlArgs = get(urlArgsAtom)
    if (urlArgs.url) {
      // store the import URL so we can display it later again
      set(importUrlBaseAtom, urlArgs.url)
    }
    if (code.length == 0) {
      // delete all url arguments if there is no code
      set(urlArgsAtom, { ...urlArgs, url: undefined, code: undefined, codez: undefined })
      return
    }
    const importedCode = get(importedCodeAtom)
    const url = get(importUrlAtom) ?? ''
    if (code == importedCode) {
      set(urlArgsAtom, {
        ...urlArgs,
        url: fixedEncodeURIComponent(url),
        code: undefined,
        codez: undefined,
      })
    } else if (get(settingsAtom).compress) {
      // LZ padds the string with trailing `=`, which mess up the argument parsing
      // and aren't needed for LZ encoding, so we remove them.
      const compressedCode = LZString.compressToBase64(code).replace(/=*$/, '')
      set(urlArgsAtom, {
        ...urlArgs,
        url: undefined,
        code: undefined,
        codez: fixedEncodeURIComponent(compressedCode),
      })
    } else {
      const encodedCode = fixedEncodeURIComponent(code)
      set(urlArgsAtom, { ...urlArgs, url: undefined, code: encodedCode, codez: undefined })
    }
  },
)
