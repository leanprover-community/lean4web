import Box from '@mui/material/Box'
import Slider from '@mui/material/Slider'
import Switch from '@mui/material/Switch'
import { useAtom } from 'jotai/react'
import { useState } from 'react'

import { Popup } from '../navigation/Popup'
import { shallowEqualSubset } from '../utils/shallowEqual'
import { applySettingsAtom, settingsAtom } from './settings-atoms'
import type { MobileValues, Theme } from './settings-types'
import { defaultSettings, Settings } from './settings-types'

export function SettingsPopup({
  open,
  handleClose,
  closeNav,
}: {
  open: boolean
  handleClose: () => void
  closeNav: () => void
}) {
  const [settings, setSettings] = useAtom(settingsAtom)
  const [, applySettings] = useAtom(applySettingsAtom)
  const [newSettings, setNewSettings] = useState<Settings>(settings)

  function updateSetting<K extends keyof Settings>(key: K, value: Settings[K]) {
    setNewSettings((prev) => ({ ...prev, [key]: value }))
  }

  return (
    <Popup open={open} handleClose={handleClose}>
      <form
        onSubmit={(ev) => {
          ev.preventDefault()
          handleClose()
          closeNav()
        }}
      >
        {/* <h2>Project settings</h2>
      <p><i>These settings are stored in the URL as they change the project's setup</i></p>
      <p>
        <label htmlFor="leanVersion">Lean Project: </label>
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
      </p> */}

        <h2>Editor settings</h2>
        <p>
          <label htmlFor="abbreviationCharacter">
            Lead character to trigger unicode input mode
          </label>
          <input
            id="abbreviationCharacter"
            type="text"
            onChange={(ev) => {
              updateSetting('abbreviationCharacter', ev.target.value)
            }}
            value={newSettings.abbreviationCharacter}
          />
        </p>
        <p>
          <Switch
            id="wordWrap"
            onChange={() => {
              updateSetting('wordWrap', !newSettings.wordWrap)
            }}
            checked={newSettings.wordWrap}
          />
          <label htmlFor="wordWrap">Wrap code</label>
        </p>
        <p>
          <Switch
            id="acceptSuggestionOnEnter"
            onChange={() => {
              updateSetting('acceptSuggestionOnEnter', !newSettings.acceptSuggestionOnEnter)
            }}
            checked={newSettings.acceptSuggestionOnEnter}
          />
          <label htmlFor="acceptSuggestionOnEnter">Accept Suggestion on Enter</label>
        </p>
        <p>
          <Switch
            id="showGoalNames"
            onChange={() => {
              updateSetting('showGoalNames', !newSettings.showGoalNames)
            }}
            checked={newSettings.showGoalNames}
          />
          <label htmlFor="showGoalNames">Show Goal Names</label>
        </p>
        <p>
          <Switch
            id="showExpectedType"
            onChange={() => {
              updateSetting('showExpectedType', !newSettings.showExpectedType)
            }}
            checked={newSettings.showExpectedType}
          />
          <label htmlFor="showExpectedType">Show Expected Type</label>
        </p>

        <h2>User settings</h2>
        <p>
          <label htmlFor="theme">Theme: </label>
          <select
            id="theme"
            name="theme"
            value={newSettings.theme}
            onChange={(ev) => {
              updateSetting('theme', ev.target.value as Theme)
            }}
          >
            <option value="Visual Studio Light">visual studio light</option>
            <option value="Visual Studio Dark">visual studio dark</option>
            {/* <option value="Default Light+">light+</option> */}
            {/* <option value="Default Dark+">dark+</option> */}
            {/* <option value="Default Light Modern">light modern</option> */}
            <option value="Default High Contrast">high contrast</option>
            <option value="Cobalt">cobalt</option>
          </select>
        </p>
        <div>
          <span>Layout: </span>
          <Box sx={{ width: 200 }}>
            <Slider
              value={mobileSliderMarks.find((item) => item.key === newSettings.mobile)?.value ?? 1}
              step={1}
              marks={mobileSliderMarks}
              max={2}
              sx={{
                '& .MuiSlider-track': { display: 'none' },
              }}
              onChange={(_, val) => {
                updateSetting('mobile', mobileSliderMarks[val].key)
              }}
            />
          </Box>
        </div>
        <p>
          <Switch
            id="compress"
            onChange={() => {
              updateSetting('compress', !newSettings.compress)
            }}
            checked={newSettings.compress}
          />
          <label htmlFor="compress">Compress code in URL</label>
        </p>
        <p>
          <Switch
            id="inUrl"
            onChange={() => {
              updateSetting('inUrl', !newSettings.inUrl)
            }}
            checked={newSettings.inUrl}
          />
          <label htmlFor="inUrl">Add settings to URL</label>
        </p>
        <h2>Save</h2>
        <p>
          <i>Editor settings and User settings are not preserved unless you opt-in to save them.</i>
        </p>
        <p>
          <Switch
            id="savingAllowed"
            onChange={() => {
              updateSetting('saved', !newSettings.saved)
            }}
            checked={newSettings.saved}
          />
          <label htmlFor="savingAllowed">Save settings (in the browser's local storage)</label>
        </p>
        <p>
          {!shallowEqualSubset(defaultSettings, newSettings) && (
            <button
              id="resetSettings"
              onClick={(e) => {
                setNewSettings({ saved: false, inUrl: false, ...defaultSettings })
                e.preventDefault()
              }}
            >
              Reset to Default
            </button>
          )}
          <input
            id="saveSettings"
            type="submit"
            value={newSettings.saved ? 'Apply & Save' : 'Apply'}
            onClick={() => applySettings(newSettings)}
          />
        </p>
      </form>
    </Popup>
  )
}

const mobileSliderMarks: { value: number; label: string; key: MobileValues }[] = [
  {
    value: 0,
    label: 'Mobile',
    key: true,
  },
  {
    value: 1,
    label: 'Auto',
    key: 'auto',
  },
  {
    value: 2,
    label: 'Desktop',
    key: false,
  },
]
