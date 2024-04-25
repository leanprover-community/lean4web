import { faGear } from '@fortawesome/free-solid-svg-icons';
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome';
import { config } from './config/config';
import * as React from 'react'
import { useEffect } from 'react'
import Switch from '@mui/material/Switch';
import Select from '@mui/material/Select';
import { useWindowDimensions } from './window_width';
import { Button, FormControl, InputLabel, MenuItem } from '@mui/material';
import * as monaco from 'monaco-editor/esm/vs/editor/editor.api.js'

const Settings: React.FC<{closeNav, theme, setTheme, project, setProject}> =
    ({closeNav, theme, setTheme, project, setProject}) => {
  const [open, setOpen] = React.useState(false);
  const handleOpen = () => setOpen(true);
  const handleClose = () => setOpen(false);

  const [abbreviationCharacter, setAbbreviationCharacter] = React.useState(config.abbreviationCharacter)

  const [savingAllowed, setSavingAllowed] = React.useState(false)

  /* Vertical layout is changeable in the settings.
    If screen width is below 800, default to vertical layout instead. */
  const {width, height} = useWindowDimensions()
  const [verticalLayout, setVerticalLayout] = React.useState(width < 800)
  const [wordWrap, setWordWrap] = React.useState(false)
  const [customTheme, setCustomTheme] = React.useState<string>('initial')

  // Synchronize state with initial local store
  useEffect(() => {
    let _abbreviationCharacter = window.localStorage.getItem("abbreviationCharacter")
    let _verticalLayout = window.localStorage.getItem("verticalLayout")
    let _wordWrap = window.localStorage.getItem("wordWrap")
    let _theme = window.localStorage.getItem("theme")
    let _savingAllowed = window.localStorage.getItem("savingAllowed")
    let _customTheme = window.localStorage.getItem("customTheme")
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
    if (_wordWrap) {
      setWordWrap(_wordWrap == "true")
      setSavingAllowed(true)
    }
    if (_customTheme) {
      setCustomTheme(_customTheme)
      setSavingAllowed(true)
      try {
        var loadedTheme = JSON.parse(_customTheme)
        monaco.editor.defineTheme('custom', loadedTheme)
      } catch (error) {
        // invalid custom theme
        setCustomTheme('')
        if (_theme == 'custom') {setTheme('lightPlus')}
      }
    }
  }, [])

  /** Synchronize config and local store whenever there is a change to any of the config
   * variables (state)
   */
  useEffect(() => {
    config.abbreviationCharacter = abbreviationCharacter
    config.verticalLayout = verticalLayout
    config.wordWrap = wordWrap
    config.theme = theme
    if (savingAllowed) {
      window.localStorage.setItem("abbreviationCharacter", abbreviationCharacter)
      window.localStorage.setItem("verticalLayout", verticalLayout ? 'true' : 'false')
      window.localStorage.setItem("wordWrap", wordWrap ? 'true' : 'false')
      window.localStorage.setItem("theme", theme)
      window.localStorage.setItem("customTheme", customTheme)
    } else {
      window.localStorage.removeItem("abbreviationCharacter")
      window.localStorage.removeItem("verticalLayout")
      window.localStorage.removeItem("wordWrap")
      window.localStorage.removeItem("theme")
      window.localStorage.removeItem("customTheme")
    }
  }, [savingAllowed, abbreviationCharacter, verticalLayout, wordWrap, theme])

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

  /** Load a custom monaco theme, store it in local storage and activate it */
  function uploadTheme(ev) {
    const fileToLoad = ev.target.files[0]
    var fileReader = new FileReader()
    fileReader.onload = (fileLoadedEvent) => {
      var loadedThemeRaw = fileLoadedEvent.target.result as string
      window.localStorage.setItem("customTheme", loadedThemeRaw)
      try {
        var loadedTheme = JSON.parse(loadedThemeRaw)
      } catch (error) {
        return
      }
      setTheme('custom')
      setCustomTheme(loadedThemeRaw)
      monaco.editor.defineTheme('custom', loadedTheme)
      monaco.editor.setTheme('custom')
    }
    fileReader.readAsText(fileToLoad, "UTF-8")
  }

  return <>
    <span className="nav-link" onClick={handleOpen}>
      <FontAwesomeIcon icon={faGear} /> Settings
    </span>
    {open?
      <div className="modal-wrapper">
        <div className="modal-backdrop" onClick={handleClose} />
        <div className="modal">
          <div className="codicon codicon-close modal-close" onClick={handleClose}></div>
          <form onSubmit={(ev) => {ev.preventDefault(); setOpen(false); closeNav()}}>
            <h2>Project settings</h2>
            <p><i>These settigns are stored in the URL as they change the project's setup</i></p>
            <p>
              <label htmlFor="leanVersion">Lean Version: </label>
              <select
                  id="leanVersion"
                  name="leanVersion"
                  value={project}
                  onChange={(ev) => {
                    setProject(ev.target.value)
                    console.log(`set Lean project to: ${ev.target.value}`)
                    }} >
                <option value="MathlibLatest">Latest Mathlib</option>
                <option value="LeanNightly">Lean nightly (without mathlib)</option>
              </select>
            </p>

            <h2>User settings</h2>
            <p><i>These settings are not preserved unless you opt-in to save them.</i></p>
            <p>
              <label htmlFor="abbreviationCharacter">Lead character to trigger unicode input mode</label>
              <input id="abbreviationCharacter" type="text"
                onChange={(ev) => {setAbbreviationCharacter(ev.target.value)}} value={abbreviationCharacter} />
            </p>
            <p className="flex">
              <label htmlFor="theme">Theme: </label>
              <select
                  id="theme"
                  name="theme"
                  value={theme}
                  onChange={(ev) => {setTheme(ev.target.value)}} >
                <option value="lightPlus">light+</option>
                <option value="GithubDark">github dark</option>
                <option value="Amy">amy</option>
                <option value="Cobalt">cobalt</option>
                <option value="custom">custom</option>
              </select>

              <label htmlFor="theme-upload" className="file-upload-button" >Load from Disk</label>
              <input id="theme-upload" type="file" onChange={uploadTheme} />

              {/* <Button variant="contained" component="label" className='file-upload-button' onClick={uploadTheme}>
                Load from Disk
                <input id="theme-upload" type="file" onChange={uploadTheme} />
              </Button> */}
            </p>
            <p>
              <Switch id="verticalLayout" onChange={handleLayoutChange} checked={verticalLayout} />
              <label htmlFor="verticalLayout">Mobile layout (vertical)</label>
            </p>
            <p>
              <Switch id="wordWrap" onChange={() => {setWordWrap(!wordWrap)}} checked={wordWrap} />
              <label htmlFor="wordWrap">Wrap code</label>
            </p>
            <p>
              <Switch id="savingAllowed" onChange={handleChangeSaving} checked={savingAllowed} />
              <label htmlFor="savingAllowed">Save my settings (in the browser store)</label>
            </p>
            <p>
              <input type="submit" value="OK" />
            </p>
          </form>
        </div>
      </div> : null
    }
  </>
}

export default Settings
