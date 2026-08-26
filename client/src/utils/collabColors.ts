const cursorColors = [
  '--vscode-charts-red',
  '--vscode-charts-blue',
  '--vscode-charts-yellow',
  '--vscode-charts-orange',
  '--vscode-charts-green',
  '--vscode-charts-purple',
]

/** Mix two base colours with some randomness to get more unique colours */
export function getCollaboratorColor(n: number) {
  const random = mulberry32(n)

  const idx1 = n % cursorColors.length
  const base = cursorColors[idx1]

  // 2nd index should not be identical to the first one
  const idx2 =
    (idx1 + 1 + Math.floor(random() * (cursorColors.length - 1))) %
    cursorColors.length
  const mixin = cursorColors[idx2]

  const amount = random() * 100

  return `color-mix(in srgb, var(${base}) ${amount}%, var(${mixin}) ${100 - amount}%) `
}

// https://github.com/cprosche/mulberry32
function mulberry32(a: number) {
  return function () {
    var t = (a += 0x6d2b79f5)
    t = Math.imul(t ^ (t >>> 15), t | 1)
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61)
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296
  }
}
