import * as React from 'react'
import { Popup } from '../Navigation'

const ToolsPopup: React.FC<{
  open: boolean
  handleClose: () => void
}> = ({open, handleClose}) => {
  return <Popup open={open} handleClose={handleClose}>
    <h2>Tools</h2>

    Add the following import to access the built-in Lean tools of the webeditor:
    <p><code>import Webeditor.Tools</code></p>

    <h3>Versions</h3>
    The following command prints the current Lean version plus all available packages
    and their current commit sha:
    <p><code>#package_version</code></p>
  </Popup>
}

export default ToolsPopup
