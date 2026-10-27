import path from 'node:path'

/**
 * Like `path.join` but ensures the resulting path is inside tha `baseDir` in order
 * to prevent path traversal
 */
export function safeJoin(baseDir, ...segments) {
  const target = path.resolve(baseDir, ...segments)
  const base = path.resolve(baseDir)
  if (target !== base && !target.startsWith(base + path.sep)) return undefined
  return target
}
