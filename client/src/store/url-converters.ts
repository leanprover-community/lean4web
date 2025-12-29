import { UrlArgs } from './url-types'

/**
 * Format the arguments for displaying in the URL, i.e. join them
 * in the form `#project=Mathlib&url=...`
 */
export function formatArgs(args: UrlArgs): string {
  let out =
    '#' +
    Object.entries(args)
      .filter(([_key, val]) => (val?.trim().length ?? 0) > 0)
      .map(([key, val]) => `${key}=${val}`)
      .join('&')
  if (out == '#') {
    return ''
  }
  return out
}

/**
 * Parse arguments from URL. These are of the form `#project=Mathlib&url=...`
 */
export function parseArgs(hash: string): UrlArgs {
  let args = hash
    .replace('#', '')
    .split('&')
    .map((s) => s.split('='))
    .filter((x) => x[0])
  return Object.fromEntries(args)
}
