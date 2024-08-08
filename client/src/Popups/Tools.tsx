import { Popup } from '../Navigation'
import { FC, useEffect, useState } from 'react'

// TODO: Do these interfaces exist somewhere in vscode-lean4?
// They might need to be updated manually if changes to `lake` occur.
interface LakePackage {
  url: string,
  type: "git",
  subDir: string,
  scope: string,
  rev: string,
  name: string,
  manifestFile: string,
  inputRev: string,
  inherited: string,
  configFile: string,
}

interface LocalLakePackage {
  type: "path",
  name: string,
  manifestFile: string,
  inherited: false,
  dir: string,
  configFile: string
}

interface LakeManifest {
  version: string,
  packagesDir: string,
  packages: (LakePackage|LocalLakePackage)[],
  name: string,
  lakeDir: string
}

/** Default. Should never actually be visible to the user as it will be overwritten immediately */
const emptyManifest: LakeManifest = {
  version: "",
  packagesDir: "",
  packages: [],
  name: "",
  lakeDir: ""
}

const ToolsPopup: FC<{
  open: boolean
  project: string
  handleClose: () => void
}> = ({open, handleClose, project}) => {

  const [manifest, setManifest] = useState<LakeManifest>(emptyManifest)
  const [toolchain, setToolchain] = useState('')
  // The last time `lake-manifest.json` has been modified
  // Experimantal: This might somewhat agree with the last update of the project
  // I couldn't think of a better way to determine this.
  const [lastModified, setLastModified] = useState<string|null>(null)

  // Load the new manifest & toolchain
  useEffect(() => {
    const urlManifest = `${window.location.origin}/api/manifest/${project}`
    fetch(urlManifest)
    .then((response) => response.json())
    .then((manifest) => {
      setManifest(manifest)
    })
    .catch( err => {
      console.error('Error reading manifest.')
      console.error(err)
    })

    const urlToolchain = `${window.location.origin}/api/toolchain/${project}`
    fetch(urlToolchain)
    .then((response) => {
      const lastModified = response.headers.get('Last-Modified')
      response.text().then(toolchain => {
        setToolchain(toolchain)
        setLastModified(lastModified)
      })
    })
    .catch( err => {
      console.error('Error reading toolchain.')
      console.error(err)
    })
  }, [project])

  return <Popup open={open} handleClose={handleClose}>
    <h2>Version</h2>
    <table>
      <tbody>
        <tr>
          <th>Last update:</th>
          <td><i>{lastModified}</i></td>
        </tr>
        <tr>
          <th>Project:</th>
          <td>{manifest.name}</td>
        </tr>
        <tr>
          <th>Toolchain:</th>
          <td>{toolchain}</td>
        </tr>
      </tbody>
    </table>
    <table>
      <tbody>
        <tr>
          <th>Packages:</th>
          <th>Commit</th>
          <th>Input Rev.</th>
        </tr>
        { manifest.packages.length > 0 ?
          manifest.packages.map(pkg => <tr key={`entry-${pkg.name}`}>
            <td>{pkg.name}</td>
            { pkg.type == 'git' ?
              <>
                <td><a href={`${pkg.url}/commits/${pkg.rev}/`} target='_blank' >{pkg.rev.substring(0,7)}</a></td>
                <td>{pkg.inputRev}</td>
              </> : <td colSpan={2}>(local package)</td>
            }
          </tr>) :
          <tr><td colSpan={3}>(no dependencies)</td></tr>
        }
      </tbody>
    </table>
    <h2>Tools</h2>
    <p>
      To see the actual Lean version implied by the toolchain above, the following can be pasted
      into the editor:
    </p>
    <pre><code>#eval Lean.versionString</code></pre>
  </Popup>
}

export default ToolsPopup
