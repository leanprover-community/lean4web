import { faHammer } from '@fortawesome/free-solid-svg-icons';
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome';
import * as React from 'react'

const Tools: React.FC = () => {
  const [open, setOpen] = React.useState(false);
  const handleOpen = () => setOpen(true);
  const handleClose = () => setOpen(false);

  return (
    <>
      <span className="nav-link" onClick={handleOpen}>
        <FontAwesomeIcon icon={faHammer} /> Tools: Version
      </span>
      {open?
        <div className="modal-wrapper">
          <div className="modal-backdrop" onClick={handleClose} />
          <div className="modal">
            <div className="codicon codicon-close modal-close" onClick={handleClose}></div>
            <h2>Tools</h2>

            Add the following import to access the built-in Lean tools of the webeditor:
            <p><code>import Webeditor.Tools</code></p>

            <h3>Versions</h3>
            The following command prints the current Lean version plus all available packages
            and their current commit sha:
            <p><code>#package_version</code></p>
          </div>
        </div> : null}
    </>
  )
}

export default Tools
