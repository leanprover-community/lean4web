import { faCodeMerge} from '@fortawesome/free-solid-svg-icons';
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome';
import { faArrowUpRightFromSquare } from '@fortawesome/free-solid-svg-icons'
import * as React from 'react'
import { useEffect } from 'react'

/*
Display the versions of Lean and all packages. This is done by copying the
`lake-manifest.json` over to the client while building the server. The copied
JSON file is called `package_versions.json`.

The Lean version is read from `lean-toolchain` and manually added to `package_versions.json`.
*/

var moment = require('moment-timezone');
var tz = Intl.DateTimeFormat().resolvedOptions().timeZone;

const Version: React.FC = () => {
  const [open, setOpen] = React.useState(false);
  const handleOpen = () => setOpen(true);
  const handleClose = () => setOpen(false);

  const [packageVersions, setPackageVersions] = React.useState(null);

  // TODO: this is hacky
  useEffect(() => {
    try {
      fetch('package_versions.json').then(function (r) {r.ok ? r.text().then(function (r) {
        if (r) {
          setPackageVersions(JSON.parse(r))
        } else {
          setPackageVersions({time : "error" , packages : [] })
        }

      }) : setPackageVersions({time : "error" , packages : [] })});
    } catch {
      console.log('rip, something with the versions file failed')
    }

  }, [])

  const readVersions = (x) => {
    let pac = x.git;
    return (
      <tr>
        <td>{pac.name}</td>
        <td>
          <a href={pac.url + "/commits/" + pac.rev} target="_blank">
            <FontAwesomeIcon icon={faArrowUpRightFromSquare} /> &nbsp;
            { (pac.name == "Lean") ? pac.rev : pac.rev.substring(0,7) }
          </a>
        </td>
      </tr>)
  }

  return (
    <span>
      <span className="nav-link" onClick={handleOpen}>
        <FontAwesomeIcon icon={faCodeMerge} /> Version
      </span>
      {open?
        <div className="modal-wrapper">
          <div className="modal-backdrop" onClick={handleClose} />
          <div className="modal">
            <div className="codicon codicon-close modal-close" onClick={handleClose}></div>
            <h2>Version</h2>
            <p>
              Lean and the available dependencies are updated automatically on a regular basis.<br/>
              Last update: { moment.unix(packageVersions.time).tz(tz).format("DD MMM. YYYY, HH:mm (z / Z)") }
            </p>
            <table>
              <tr>
                <th>Package</th>
                <th>Commit</th>
              </tr>
              { packageVersions.packages.map(readVersions) }
            </table>
          </div>
        </div> : null}
    </span>
  )
}

export default Version
