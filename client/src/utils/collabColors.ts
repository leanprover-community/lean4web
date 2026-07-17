const cursorColors = [
  '--vscode-charts-red',
  '--vscode-charts-blue',
  '--vscode-charts-yellow',
  '--vscode-charts-orange',
  '--vscode-charts-green',
  '--vscode-charts-purple',
]

export function getCollaboratorColor(n: number) {
  return cursorColors[n % cursorColors.length]
}
