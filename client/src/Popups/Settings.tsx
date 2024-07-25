import * as React from 'react'
import { useContext, useEffect } from 'react'
// import settings from '../config/settings';
import Switch from '@mui/material/Switch';
import { useWindowDimensions } from '../utils/window_width';
import * as monaco from 'monaco-editor/esm/vs/editor/editor.api.js'
import lean4webConfig from '../config/config'
import { Popup } from '../Navigation';
import defaultSettings from '../config/settings'

/** This must be kept in sync with ../config/settings.ts */
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

/** The context holding the preferences */
export const PreferencesContext = React.createContext<{
  preferences: IPreferencesContext,
  setPreferences: React.Dispatch<React.SetStateAction<IPreferencesContext>>
}>({
  preferences: defaultSettings,
  setPreferences: () => {}
})

/** Save preferences to local storage whenever there are modifications */
function savePreferences(preferences: IPreferencesContext) {
  console.debug("Preferences: Saving.")
  if (preferences.saveInLocalStore) {
    for (const [key, value] of Object.entries(preferences)) {
      if (typeof value === 'string') {
        window.localStorage.setItem(key, value)
      } else if (typeof value === 'boolean') {
        // turn boolean values into string
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
}

const SettingsPopup: React.FC<{
  open: boolean
  handleClose: () => void
  closeNav: () => void
  project: any
  setProject: any
}> = ({open, handleClose, closeNav, project, setProject}) => {
  const { preferences, setPreferences } = useContext(PreferencesContext)

  function modifyPreferences(key: keyof IPreferencesContext, value: any) {
    let newPreferences: any = { ...preferences }
    newPreferences[key] = value
    setPreferences(newPreferences)
  }

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
        <input type="submit" value={preferences.saveInLocalStore?"Save":"OK"} onClick={() => {savePreferences(preferences)}}/>
      </p>
    </form>
  </Popup>
}

export default SettingsPopup
