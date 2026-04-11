import { atom } from 'jotai'
import { atomWithQuery } from 'jotai-tanstack-query'

import { fixedEncodeURIComponent, lookupUrl } from '../utils/UrlParsing'
import { currentProjectAtom } from './project-atoms'
import { urlArgsAtom, urlArgsStableAtom } from './url-atoms'

/**
 * Stores the import-URL.
 *
 * This is needed for the comparison which puts the URL back into the location hash if
 * the current code matches the one from the import-URL.
 */
export const importUrlBaseAtom = atom<string>()

/**
 *
 *
 */
export const importUrlAtom = atom(
  (get) => get(urlArgsStableAtom).url ?? get(importUrlBaseAtom),
  (get, set, url: string) => {
    const urlArgs = get(urlArgsStableAtom)
    set(importUrlBaseAtom, url)
    set(urlArgsAtom, {
      ...urlArgs,
      url: fixedEncodeURIComponent(url),
      code: undefined,
      codez: undefined,
    })
  },
)

/** Query to fetch the code from the import URL */
const importedCodeQueryAtom = atomWithQuery((get) => {
  const url = get(importUrlAtom)
  return {
    queryKey: ['importedCode', url],
    queryFn: async () => {
      if (!url) return undefined
      const res = await fetch(lookupUrl(url))
      const code = res.ok ? await res.text() : `Error: failed to load code from ${url}`
      return code
    },
    enabled: url != undefined,
    keepPreviousData: true,
  }
})

/**
 * Stores the imported code.
 *
 * This is needed for the comparison which puts the URL back into the location hash if
 * the current code matches the one from the import-URL.
 */
export const importedCodeAtom = atom((get) => {
  const { data } = get(importedCodeQueryAtom)
  return data
})

/**
 * Load code from the import URL and run it with the specified project.
 *
 * If no project is provided, the project remains unchanged.
 */
export const setImportUrlAndProjectAtom = atom(
  null,
  (get, set, val: { url: string; project?: string }) => {
    set(importUrlAtom, val.url) // TODO: should there be some decoding of the input?
    if (val.project) {
      set(currentProjectAtom, val.project)
    }
  },
)
