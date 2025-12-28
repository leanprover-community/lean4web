import lean4webConfig from '../config/config'
import { Popup } from '../navigation/Popup'

/** The popup with the privacy policy. */
function ImpressumPopup({ open, handleClose }: { open: boolean; handleClose: () => void }) {
  return (
    <Popup open={open} handleClose={handleClose}>
      <h2>Impressum</h2>

      {lean4webConfig.contactDetails && (
        <p>
          <strong>Contact details</strong>
          <br />
          {lean4webConfig.contactDetails}
        </p>
      )}

      {lean4webConfig.impressum}
    </Popup>
  )
}

export default ImpressumPopup
