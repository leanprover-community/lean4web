import { atom } from 'jotai'
import { atomWithQuery } from 'jotai-tanstack-query'

import { lookupUrl } from '../utils/UrlParsing'
import { urlArgsAtom, urlArgsStableAtom } from './url-atoms'

/**
 * Stores the import-URL.
 *
 * This is needed for the comparison which puts the URL back into the location hash if
 * the current code matches the one from the import-URL.
 */
export const importUrlAtom = atom<string>()

/**
 * Stores the imported code.
 *
 * This is needed for the comparison which puts the URL back into the location hash if
 * the current code matches the one from the import-URL.
 */
export const importedCodeAtom = atom<string>()

/** Query to fetch the code from the import URL */
const freshlyImportedCodeQueryAtom = atomWithQuery((get) => {
  const url = get(urlArgsStableAtom).url
  return {
    queryKey: ['importedCode', url],
    queryFn: async () => {
      if (!url) return undefined
      const res = await fetch(lookupUrl(url))
      const code = res.ok ? await res.text() : `Error: failed to load code from ${url}`
      return code
    },
    enabled: url !== undefined,
    keepPreviousData: true,
  }
})

export const freshlyImportedCodeAtom = atom((get) => {
  const { data } = get(freshlyImportedCodeQueryAtom)
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
    const urlArgs = get(urlArgsStableAtom)
    set(urlArgsAtom, {
      ...urlArgs,
      url: val.url,
      project: val.project ?? urlArgs.project,
      code: undefined,
      codez: undefined,
    })
  },
)
