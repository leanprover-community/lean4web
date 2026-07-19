import { saveAs } from 'file-saver'
import JSZip from 'jszip'

/**
 * If a `project` is provided, downloads a complete Lake project as a ZIP.
 * Otherwise downloads a single Lean file.
 */
export async function save(content: string, project?: string) {
  const mainFile = new Blob([content], { type: 'text/plain;charset=utf-8' })

  // Single-file download
  if (!project) {
    saveAs(mainFile, 'LeanWebDownload.lean')
    return
  }

  const projectFiles = [
    { endpoint: 'manifest', filename: 'lake-manifest.json' },
    { endpoint: 'toolchain', filename: 'lean-toolchain' },
    { endpoint: 'lakefile', filename: 'lakefile.lean' },
    { endpoint: 'lakefile-toml', filename: 'lakefile.toml' },
  ]

  const fetchedFiles = await Promise.all(
    projectFiles.map(async ({ endpoint, filename }) => {
      try {
        const response = await fetch(
          `${window.location.origin}/api/${endpoint}/${project}`,
        )
        if (!response.ok) return undefined
        return {
          filename,
          content: await response.text(),
        }
      } catch {
        return undefined
      }
    }),
  )

  const zip = new JSZip()
  const root = zip.folder(project)

  // The editor content
  root?.file(`${project}.lean`, mainFile)

  // Additional project files
  fetchedFiles.forEach((file) => {
    if (!file) return

    root?.file(file.filename, file.content)
  })

  const zipBlob = await zip.generateAsync({ type: 'blob' })
  saveAs(zipBlob, `${project}.zip`)
}
