import { faGear } from '@fortawesome/free-solid-svg-icons';
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome';
import { config } from './editor/abbreviation/config';
import * as React from 'react'

const Settings: React.FC = () => {
  const [open, setOpen] = React.useState(false);
  const handleOpen = () => setOpen(true);
  const handleClose = () => setOpen(false);

  return (
    <span>
      <span className="nav-link" onClick={handleOpen}>
        <FontAwesomeIcon icon={faGear} /> Settings
      </span>
      {open?
        <div className="modal-wrapper">
          <div className="modal-backdrop" onClick={handleClose} />
          <div className="modal">
            <div className="codicon codicon-close modal-close" onClick={handleClose}></div>
            <h2>Settings</h2>
            <form onSubmit={(ev) => {ev.preventDefault(); setOpen(false)}}>
            <label htmlFor="abbreviationCharacter">Lead character to trigger unicode input mode</label>
            <input name="abbreviationCharacter" type="text" onChange={(ev) => {config.abbreviationCharacter = ev.target.value}}  defaultValue={config.abbreviationCharacter} />
            <input type="submit" value="OK"/>
            </form>
          </div>
        </div> : null}
    </span>
  )
}

export default Settings
