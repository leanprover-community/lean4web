/** Escape `(` and `)` in URL. */
export function fixedEncodeURIComponent(str: string) {
  return encodeURIComponent(str).replace(/[()]/g, function (c) {
    return '%' + c.charCodeAt(0).toString(16)
  })
}

/**
 * Tries to lookup and replace some common URLs, such as a github url.
 *
 * - change link to github file to its raw content.
 */
export function lookupUrl(url: string): string {
  const regex = RegExp('https://github.com/(.+)/blob/(.+)')

  if (regex.test(url)) {
    url = url.replace(regex, 'https://raw.githubusercontent.com/$1/refs/heads/$2')
  }

  return url
}
