import { faGear } from '@fortawesome/free-solid-svg-icons';
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome';
import { config } from './editor/abbreviation/config';
import * as React from 'react'
import { useEffect } from 'react'

const Settings: React.FC = () => {
  const [open, setOpen] = React.useState(false);
  const handleOpen = () => setOpen(true);
  const handleClose = () => setOpen(false);

  const [abbreviationCharacter, setAbbreviationCharacter] =
    React.useState(config.abbreviationCharacter);
  const [cookiesAllowed, setCookiesAllowed] = React.useState(false);

  // Synchronize state with initial cookies
  useEffect(() => {
    let abbreviationCharacter = window.localStorage.getItem("abbreviationCharacter")
    if (abbreviationCharacter) {
      setAbbreviationCharacter(abbreviationCharacter)
      setCookiesAllowed(true)
    }
  }, [])

  // Synchronize config and cookies with state
  useEffect(() => {
    config.abbreviationCharacter = abbreviationCharacter
    if (cookiesAllowed) {
      window.localStorage.setItem("abbreviationCharacter", abbreviationCharacter)
    } else {
      window.localStorage.removeItem("abbreviationCharacter")
    }
  }, [cookiesAllowed, abbreviationCharacter])

  const handleChangeCookie = (ev) => {
    if (ev.target.checked) {
      setCookiesAllowed(true)
    } else {
      setCookiesAllowed(false)
    }
  }

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
              <p>
                <label htmlFor="abbreviationCharacter">Lead character to trigger unicode input mode</label>
                <input id="abbreviationCharacter" type="text"
                  onChange={(ev) => {setAbbreviationCharacter(ev.target.value)}}  value={abbreviationCharacter} />
              </p>
              <p>
                <input id="cookiesAllowed" type="checkbox" onChange={handleChangeCookie} checked={cookiesAllowed}/> <label htmlFor="cookiesAllowed">Save my settings in a cookie</label>
                <input type="submit" value="OK"/>
              </p>
            </form>
          </div>
        </div> : null}
    </span>
  )
}

export default Settings
