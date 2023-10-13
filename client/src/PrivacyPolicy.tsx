import { faShield } from '@fortawesome/free-solid-svg-icons';
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome';
import * as React from 'react'

const PrivacyPolicy: React.FC = () => {
  const [open, setOpen] = React.useState(false);
  const handleOpen = () => setOpen(true);
  const handleClose = () => setOpen(false);

  return (
    <span>
      <span className="nav-link" onClick={handleOpen}>
        <FontAwesomeIcon icon={faShield} />Privacy policy
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

            <p>Our server is located in Germany.</p>

            <p><strong>Contact information:</strong><br />
              <a href="https://www.math.hhu.de/lehrstuehle-/-personen-/-ansprechpartner/innen/lehrstuehle-des-mathematischen-instituts/lehrstuhl-fuer-algebraische-geometrie/team/dr-alexander-bentkamp">Alexander Bentkamp</a>,&nbsp;
              <a href="https://www.math.hhu.de/lehrstuehle-/-personen-/-ansprechpartner/innen/lehrstuehle-des-mathematischen-instituts/lehrstuhl-fuer-algebraische-geometrie/team/jon-eugster">Jon Eugster</a><br />
              Mathematisches Institut der Heinrich-Heine-Universität Düsseldorf<br />
              Universitätsstr. 1<br />
              40225 Düsseldorf<br />
              Germany<br />
              +49 211 81-12173<br />
            </p>
          </div>
        </div> : null}
    </span>
  )
}

export default PrivacyPolicy
