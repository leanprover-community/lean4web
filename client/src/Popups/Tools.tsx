import * as React from 'react'
import { Popup } from '../Navigation'
import { useEffect, useState } from 'react'

// TODO: Do these interfaces exist somewhere in vscode-lean4?
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

/** Default. Should never actually be used as it will be overwritten immediately */
const emptyManifest: LakeManifest = {
  version: "",
  packagesDir: "",
  packages: [],
  name: "",
  lakeDir: ""
}

const ToolsPopup: React.FC<{
  open: boolean
  project: string
  handleClose: () => void
}> = ({open, handleClose, project}) => {

  const [manifest, setManifest] = useState<LakeManifest>(emptyManifest)
  const [toolchain, setToolchain] = useState('')

  useEffect(() => {
    const url = `${window.location.origin}/api/manifest/${project}`
    fetch(url)
    .then((response) => response.json())
    .then((manifest) => {
      setManifest(manifest)
    })
    .catch( err => {
      console.error(err)
    })

    const url2 = `${window.location.origin}/api/toolchain/${project}`
    fetch(url2)
    .then((response) => response.text())
    .then((toolchain) => {
      setToolchain(toolchain)
    })
    .catch( err => {
      console.error(err)
    })
  }, [project])

  return <Popup open={open} handleClose={handleClose}>
    <h2>Version</h2>
    <table>
      <tr>
        <th>Project:</th>
        <td>{manifest.name}</td>
      </tr>
      <tr>
        <th>Lean:</th>
        <td>{toolchain}</td>
      </tr>
    </table>
    <table>
      <tr>
        <th>Packages</th>
        <th>Commit</th>
        <th>Input Rev.</th>
      </tr>
      { manifest.packages.map(pkg => <tr>
        <td>{pkg.name}</td>
        { pkg.type == 'git' ?
          <>
            <td><a href={`${pkg.url}/commits/${pkg.rev}/`} target='_blank' >{pkg.rev.substring(0,7)}</a></td>
            <td>{pkg.inputRev}</td>
          </> : <td colSpan={2}>(local package)</td>
        }
      </tr>)}
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
