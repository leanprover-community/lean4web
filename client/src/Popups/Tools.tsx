import { useEffect, useRef, useState } from 'react'

import { Popup } from '../navigation/Popup'

// TODO: Do these interfaces exist somewhere in vscode-lean4?
// They might need to be updated manually if changes to `lake` occur.
interface LakePackage {
  url: string
  type: 'git'
  subDir: string
  scope: string
  rev: string
  name: string
  manifestFile: string
  inputRev: string
  inherited: string
  configFile: string
}

interface LocalLakePackage {
  type: 'path'
  name: string
  manifestFile: string
  inherited: false
  dir: string
  configFile: string
}

interface LakeManifest {
  version: string
  packagesDir: string
  packages: (LakePackage | LocalLakePackage)[]
  name: string
  lakeDir: string
}

/** Default. Should never actually be visible to the user as it will be overwritten immediately */
const emptyManifest: LakeManifest = {
  version: '',
  packagesDir: '',
  packages: [],
  name: '',
  lakeDir: '',
}

/** These are just a few relevant fields the data fetched from github comprises. */
interface CommitInfo {
  sha: string
  commit: {
    author: {
      name: string
      date: string
    }
    message: string
  }
  author: {
    avatar_url: string
  }
  stats: {
    total: number
    additions: number
    deletions: number
  }
}

/** Displays a link of the specified commit together with a hover-tooltip showing the
 * information from github.
 *
 * Note that github has a rate limit (60 requests/h), but since this should be a
 * rarely used feature, it might be fine for now.
 */
function ToolTip({ pkg }: { pkg: LakePackage }) {
  const [loaded, setLoaded] = useState(false)
  const linkRef = useRef<HTMLAnchorElement>(null)
  const [commit, setCommit] = useState<CommitInfo>()
  const [error, setError] = useState<string>()

  // Load commit info on hovering the first time
  const handleHover = (_event: any) => {
    // Do not fetch twice
    if (loaded) {
      return
    }
    setLoaded(true)

    // construct github api URL from repo URL
    let m = pkg.url.match(/github.com\/([^\/]+)\/([^\/\.]+)/i) // exclude '\.' to strip potential '.git' at the end
    if (!m || m.length < 2) {
      console.warn(`[LeanWeb]: cannot parse package url`, pkg.url)
      setError('Not Found')
      return
    }

    let githubUrl = `https://api.github.com/repos/${m![1]}/${m![2]}/commits/${pkg.rev}`

    pkg.url.replace('github.com/', 'api.github.com/repos/') + `/commits/${pkg.rev}`
    console.debug(`[LeanWeb]: fetch from ${githubUrl}`)

    fetch(githubUrl)
      .then((response) => {
        if (!response.ok) {
          console.warn(`[LeanWeb]: failed request (${response.status})`, response)
        }
        return response.json()
      })
      .then((data) => {
        if (data.message) {
          // e.g. when reaching rate limit
          setError(data.message)
        } else {
          setCommit(data)
        }
      })
      .catch((error) => {
        setError(error)
        console.error(error)
      })
  }

  useEffect(() => {
    linkRef.current?.addEventListener('mouseover', handleHover)
    return () => {
      linkRef.current?.removeEventListener('mouseover', handleHover)
    }
  }, [linkRef, loaded])

  return (
    <a ref={linkRef} className="tooltip" href={`${pkg.url}/commits/${pkg.rev}/`} target="_blank">
      {pkg.rev.substring(0, 7)}
      <div className="tooltiptext" id="tooltip-content">
        {error ? (
          <p>{error}</p>
        ) : loaded && commit ? (
          <>
            {/* valid */}
            <img src={commit?.author?.avatar_url} />
            <p>
              <span className="commit-date">
                {new Date(commit?.commit?.author?.date).toLocaleString()}
              </span>
              <br />
              <span className="commit-message">{commit?.commit?.message.split('\n')[0]}</span>{' '}
              <span className="commit-author">by {commit?.commit?.author?.name}</span>
              <br />
              <span className="commit-sha">{commit?.sha}</span>
            </p>
          </>
        ) : (
          <p>Loading…</p>
        )}
      </div>
    </a>
  )
}

/** Shows important information about the Lean project loaded in the web editor */
function ToolsPopup({
  open,
  handleClose,
  project,
}: {
  open: boolean
  project: string
  handleClose: () => void
}) {
  const [manifest, setManifest] = useState<LakeManifest>(emptyManifest)
  const [toolchain, setToolchain] = useState('')
  // The last time `lake-manifest.json` has been modified
  // Experimental: This might somewhat agree with the last update of the project
  // I couldn't think of a better way to determine this.
  const [lastModified, setLastModified] = useState<string | null>(null)

  // Load the new manifest & toolchain
  useEffect(() => {
    if (!project) {
      return
    }
    const urlManifest = `${window.location.origin}/api/manifest/${project}`
    fetch(urlManifest)
      .then((response) => {
        var _lastModified = response.headers.get('Last-Modified')
        response.json().then((manifest) => {
          setManifest(manifest)
          setLastModified(_lastModified)
        })
      })
      .catch((err) => {
        console.error('Error reading manifest.')
        console.error(err)
      })

    const urlToolchain = `${window.location.origin}/api/toolchain/${project}`
    fetch(urlToolchain)
      .then((response) => {
        response.text().then((toolchain) => {
          setToolchain(toolchain)
        })
      })
      .catch((err) => {
        console.error('Error reading toolchain.')
        console.error(err)
      })
  }, [project])

  return (
    <Popup open={open} handleClose={handleClose}>
      <h2>Version</h2>
      <table>
        <tbody>
          <tr>
            <th>Last (manifest) update:</th>
            <td>
              <i>{lastModified}</i>
            </td>
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
          {manifest.packages.length > 0 ? (
            manifest.packages.map((pkg) => (
              <tr key={`entry-${pkg.name}`}>
                <td>{pkg.name}</td>
                {pkg.type == 'git' ? (
                  <>
                    <td>
                      <ToolTip pkg={pkg} />
                    </td>
                    <td>{pkg.inputRev}</td>
                  </>
                ) : (
                  <td colSpan={2}>(local package)</td>
                )}
              </tr>
            ))
          ) : (
            <tr>
              <td colSpan={3}>(no dependencies)</td>
            </tr>
          )}
        </tbody>
      </table>
      <h2>Tools</h2>
      <p>
        To see the actual Lean version implied by the toolchain above, the following can be pasted
        into the editor:
      </p>
      <pre>
        <code>#eval Lean.versionString</code>
      </pre>
    </Popup>
  )
}

export default ToolsPopup
