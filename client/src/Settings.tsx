import { faGear } from '@fortawesome/free-solid-svg-icons';
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome';
import { config } from './config/config';
import * as React from 'react'
import { useEffect } from 'react'
import Switch from '@mui/material/Switch';
import { useWindowDimensions } from './window_width';

const Settings: React.FC<{closeNav, theme, setTheme}> =
    ({closeNav, theme, setTheme}) => {
  const [open, setOpen] = React.useState(false);
  const handleOpen = () => setOpen(true);
  const handleClose = () => setOpen(false);

  const [abbreviationCharacter, setAbbreviationCharacter] = React.useState(config.abbreviationCharacter)

  const [savingAllowed, setSavingAllowed] = React.useState(false)

  /* Vertical layout is changeable in the settings.
    If screen width is below 800, default to vertical layout instead. */
  const {width, height} = useWindowDimensions()
  const [verticalLayout, setVerticalLayout] = React.useState(width < 800)

  // Synchronize state with initial local store
  useEffect(() => {
    let _abbreviationCharacter = window.localStorage.getItem("abbreviationCharacter")
    let _verticalLayout = window.localStorage.getItem("verticalLayout")
    let _theme = window.localStorage.getItem("theme")
    let _savingAllowed = window.localStorage.getItem("savingAllowed")
    if (_abbreviationCharacter) {
      setAbbreviationCharacter(_abbreviationCharacter)
      setSavingAllowed(true)
    }
    if (_verticalLayout) {
      setVerticalLayout(_verticalLayout == 'true')
      setSavingAllowed(true)
    }
    if (_theme) {
      setTheme(_theme)
      setSavingAllowed(true)
    }

  }, [])

  /** Synchronize config and local store whenever there is a change to any of the config
   * variables (state)
   */
  useEffect(() => {
    config.abbreviationCharacter = abbreviationCharacter
    config.verticalLayout = verticalLayout
    config.theme = theme
    if (savingAllowed) {
      window.localStorage.setItem("abbreviationCharacter", abbreviationCharacter)
      window.localStorage.setItem("verticalLayout", verticalLayout ? 'true' : 'false')
      window.localStorage.setItem("theme", theme)
    } else {
      window.localStorage.removeItem("abbreviationCharacter")
      window.localStorage.removeItem("verticalLayout")
      window.localStorage.removeItem("theme")
    }
  }, [savingAllowed, abbreviationCharacter, verticalLayout, theme])

  const handleChangeSaving = (ev) => {
    if (ev.target.checked) {
      setSavingAllowed(true)
    } else {
      setSavingAllowed(false)
    }
  }

  const handleLayoutChange = (ev: React.ChangeEvent<HTMLInputElement>) => {
    setVerticalLayout(!verticalLayout)
  //  ev.stopPropagation()
  }

  const handleThemeChange = (ev: React.ChangeEvent<HTMLInputElement>) => {
    if (theme == 'dark') {
      setTheme('light')
    } else {
      setTheme('dark')
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
            <form onSubmit={(ev) => {ev.preventDefault(); setOpen(false); closeNav()}}>
              <p>
                <label htmlFor="abbreviationCharacter">Lead character to trigger unicode input mode</label>
                <input id="abbreviationCharacter" type="text"
                  onChange={(ev) => {setAbbreviationCharacter(ev.target.value)}} value={abbreviationCharacter} />
              </p>
              <p>
                <Switch id="verticalLayout" onChange={handleLayoutChange} checked={verticalLayout} />
                <label htmlFor="verticalLayout">Mobile layout (vertical)</label>
              </p>
              <p>
                <Switch id="theme" onChange={handleThemeChange} checked={theme == 'dark'} />
                <label htmlFor="theme">Dark theme</label>
              </p>
              <p>
                <Switch id="savingAllowed" onChange={handleChangeSaving} checked={savingAllowed} />
                <label htmlFor="savingAllowed">Save my settings (in the browser store)</label>
                <input type="submit" value="OK" />
              </p>
            </form>
          </div>
        </div> : null}
    </span>
  )
}

export default Settings
