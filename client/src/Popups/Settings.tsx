import * as React from 'react'
import { useContext, useEffect } from 'react'
// import settings from '../config/settings';
import Switch from '@mui/material/Switch';
import { useWindowDimensions } from '../utils/window_width';
import * as monaco from 'monaco-editor/esm/vs/editor/editor.api.js'
import lean4webConfig from '../config/config'
import { Popup } from '../Navigation';
import defaultSettings from '../config/settings'

export interface IPreferencesContext {
  // lean4web
  mobile: boolean
  saveInLocalStore: boolean
  // editor
  acceptSuggestionOnEnter: boolean
  wordWrap: boolean,
  theme: string,
  // lean4
  abbreviationCharacter: string
}

export const PreferencesContext = React.createContext<{
  preferences: IPreferencesContext,
  setPreferences: React.Dispatch<React.SetStateAction<IPreferencesContext>>
}>({
  preferences: defaultSettings,
  setPreferences: () => {}
})

const SettingsPopup: React.FC<{
  open: boolean
  handleClose: () => void
  closeNav: () => void
  project: any
  setProject: any
}> = ({open, handleClose, closeNav, project, setProject}) => {

  const { preferences, setPreferences } = useContext(PreferencesContext)
  // const [abbreviationCharacter, setAbbreviationCharacter] = React.useState(preferences.abbreviationCharacter)

  /* Vertical layout is changeable in the settings.
    If screen width is below 800, default to vertical layout instead. */
  // const {width, height} = useWindowDimensions()
  // const [mobile, setVerticalLayout] = React.useState(width < 800)
  // const [wordWrap, setWordWrap] = React.useState(true)
  // const [acceptSuggestionOnEnter, setAcceptSuggestionOnEnter] = React.useState(false)

  // Synchronize state with initial local store
  useEffect(() => {



    // let _abbreviationCharacter = window.localStorage.getItem("abbreviationCharacter")
    // let _mobile = window.localStorage.getItem("mobile")
    // let _wordWrap = window.localStorage.getItem("wordWrap")
    // let _acceptSuggestionOnEnter = window.localStorage.getItem("acceptSuggestionOnEnter")
    // let _theme = window.localStorage.getItem("theme")
    // let _savingAllowed = window.localStorage.getItem("savingAllowed")
    // let _customTheme = window.localStorage.getItem("customTheme")
    // if (_abbreviationCharacter) {
    //   setAbbreviationCharacter(_abbreviationCharacter)
    //   setSavingAllowed(true)
    // }
    // if (_mobile) {
    //   setVerticalLayout(_mobile == 'true')
    //   setSavingAllowed(true)
    // }
    // if (_theme) {
    //   setTheme(_theme)
    //   setSavingAllowed(true)
    // }
    // if (_wordWrap) {
    //   setWordWrap(_wordWrap == "true")
    //   setSavingAllowed(true)
    // }
    // if (_acceptSuggestionOnEnter) {
    //   setAcceptSuggestionOnEnter(_acceptSuggestionOnEnter == "true")
    //   setSavingAllowed(true)
    // }
    // if (_customTheme) {
    //   setCustomTheme(_customTheme)
    //   setSavingAllowed(true)
    //   try {
    //     var loadedTheme = JSON.parse(_customTheme)
    //     monaco.editor.defineTheme('custom', loadedTheme)
    //   } catch (error) {
    //     // invalid custom theme
    //     setCustomTheme('')
    //     if (_theme == 'custom') {setTheme('lightPlus')}
    //   }
    // }
  }, [])

  function modifyPreferences(key: keyof IPreferencesContext, value: any) {
    let newPreferences: any = { ...preferences }
    newPreferences[key] = value
    setPreferences(newPreferences)
  }

  /** Store preferences to local storage whenever there are modifications */
  useEffect(() => {
    if (preferences.saveInLocalStore) {
      for (const [key, value] of Object.entries(preferences)) {
        if (typeof value === 'string') {
          window.localStorage.setItem(key, value)
        } else if (typeof value === 'boolean') {
          // Boolean values
          window.localStorage.setItem(key, value ? 'true' : 'false')
        } else {
          // other values aren't implemented yet.
          console.error(`Preferences contain a value of unsupported type: ${typeof value}`)
        }
      }
    } else {
      for (const key in preferences) {
        window.localStorage.removeItem(key)
      }
    }
  }, [preferences])

  return <Popup open={open} handleClose={handleClose}>
    <form onSubmit={(ev) => {ev.preventDefault(); handleClose(); closeNav()}}>
      <h2>Project settings</h2>
      <p><i>These settings are stored in the URL as they change the project's setup</i></p>
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
          {lean4webConfig.projects.map(proj =>
            <option key={proj.folder} value={proj.folder}>{proj.name ?? proj.folder}</option>
          )}
        </select>
      </p>

      <h2>User settings</h2>
      <p><i>These settings are not preserved unless you opt-in to save them.</i></p>
      <p>
        <label htmlFor="abbreviationCharacter">Lead character to trigger unicode input mode</label>
        <input id="abbreviationCharacter" type="text"
          onChange={(ev) => {modifyPreferences("abbreviationCharacter", ev.target.value)}}
          value={preferences.abbreviationCharacter} />
      </p>
      <p className="flex">
        <label htmlFor="theme">Theme: </label>
        <select
            id="theme"
            name="theme"
            value={preferences.theme}
            onChange={(ev) => {modifyPreferences("theme", ev.target.value)}}
            >
          <option value="Default Light+">light+</option>
          {/* <option value="Default Light Modern">light modern</option> */}
          <option value="Default Dark+">dark+</option>
          <option value="Default High Contrast">high contrast</option>
          <option value="Cobalt">cobalt</option>
          {/* <option value="Visual Studio Light">visual studio light</option> */}
          {/* <option value="Visual Studio Dark">visual studio dark</option> */}
        </select>

        {/* <label htmlFor="theme-upload" className="file-upload-button" >Load from Disk</label>
        <input id="theme-upload" type="file" onChange={uploadTheme} /> */}

        {/* <Button variant="contained" component="label" className='file-upload-button' onClick={uploadTheme}>
          Load from DisksetTheme
          <input id="theme-upload" type="file" onChange={uploadTheme} />
        </Button> */}
      </p>
      <p>
        <Switch id="mobile" onChange={() => {
          modifyPreferences("mobile", !preferences.mobile)
          // ev.stopPropagation()
        }} checked={preferences.mobile}
        />
        <label htmlFor="mobile">Mobile layout (vertical)</label>
      </p>
      <p>
        <Switch id="wordWrap" onChange={() => {modifyPreferences("wordWrap", !preferences.wordWrap)}}
        checked={preferences.wordWrap} />
        <label htmlFor="wordWrap">Wrap code</label>
      </p>
      <p>
        <Switch id="acceptSuggestionOnEnter" onChange={() => {modifyPreferences("acceptSuggestionOnEnter", !preferences.acceptSuggestionOnEnter)}}
        checked={preferences.acceptSuggestionOnEnter} />
        <label htmlFor="acceptSuggestionOnEnter">Accept Suggestion on Enter</label>
      </p>
      <p>
        <Switch id="savingAllowed" onChange={() => {modifyPreferences("saveInLocalStore", !preferences.saveInLocalStore)}} checked={preferences.saveInLocalStore} />
        <label htmlFor="savingAllowed">Save my settings (in the browser store)</label>
      </p>
      <p>
        <input type="submit" value="OK" />
      </p>
    </form>
  </Popup>
}

export default SettingsPopup
