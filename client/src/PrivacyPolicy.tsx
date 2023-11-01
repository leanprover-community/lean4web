import { faShield } from '@fortawesome/free-solid-svg-icons';
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome';
import * as React from 'react'
import { text } from './config/text';

const PrivacyPolicy: React.FC = () => {
  const [open, setOpen] = React.useState(false);
  const handleOpen = () => setOpen(true);
  const handleClose = () => setOpen(false);

  return <>
    <span className="nav-link" onClick={handleOpen}>
      <FontAwesomeIcon icon={faShield} />&nbsp;Privacy policy
    </span>
    {open?
      <div className="modal-wrapper">
        <div className="modal-backdrop" onClick={handleClose} />
        <div className="modal">
          <div className="codicon codicon-close modal-close" onClick={handleClose}></div>
          <h2>Privacy Policy</h2>

          <p>Our server collects metadata (such as IP address, browser, operating system)
          and the data that the user enters into the editor. The data is used to
          compute the Lean output and display it to the user. The information will be stored
          as long as the user stays on our website and will be deleted immediately afterwards.
          We keep logs to improve our software, but the contained data is anonymized.</p>

          <p>We don't use cookies but you can choose to save the settings in the browser store
            by activating the option in the settings.
          </p>

          { text.serverCountry &&
            <p>Our server is located in {text.serverCountry}.</p>
          }

          { text.contactInformation &&
            <p>
              <strong>Contact information:</strong><br/>
              {text.contactInformation}
            </p>
          }
        </div>
      </div> : null}
  </>
}

export default PrivacyPolicy
