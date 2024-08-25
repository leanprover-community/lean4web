import { FC } from 'react'
import { Popup } from '../Navigation'
import lean4webConfig from '../config/config'

/** The popup with the privacy policy. */
const ImpressumPopup: FC<{
  open: boolean
  handleClose: () => void
}> = ({open, handleClose}) => {
  return <Popup open={open} handleClose={handleClose}>
    <h2>Impressum</h2>

    { lean4webConfig.contactDetails &&
      <p>
        <strong>Contact details</strong><br/>
        {lean4webConfig.contactDetails}
      </p>
    }

    { lean4webConfig.impressum }
  </Popup>
}

export default ImpressumPopup
