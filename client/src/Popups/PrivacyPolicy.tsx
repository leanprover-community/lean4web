import * as React from 'react'
import { Popup } from '../Navigation'
import lean4webConfig from '../config/config'

/** The popup with the privacy policy. */
const PrivacyPopup: React.FC<{
  open: boolean
  handleClose: () => void
}> = ({open, handleClose}) => {
  return <Popup open={open} handleClose={handleClose}>
    <h2>Privacy Policy</h2>

    <p>Our server collects metadata (such as IP address, browser, operating system)
    and the data that the user enters into the editor. The data is used to
    compute the Lean output and display it to the user. The information will be stored
    as long as the user stays on our website and will be deleted immediately afterwards.
    We keep logs to improve our software, but the contained data is anonymized.</p>

    <p>We don't use cookies but you can choose to save the settings in the browser store
      by activating the option in the settings.
    </p>

    { lean4webConfig.serverCountry &&
      <p>Our server is located in {lean4webConfig.serverCountry}.</p>
    }

    { lean4webConfig.contactInformation &&
      <p>
        <strong>Contact information:</strong><br/>
        {lean4webConfig.contactInformation}
      </p>
    }
  </Popup>
}

export default PrivacyPopup
