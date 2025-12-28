import saveAs from 'file-saver'

export const save = (content: string) => {
  var blob = new Blob([content], { type: 'text/plain;charset=utf-8' })
  saveAs(blob, 'Lean4WebDownload.lean')
}
