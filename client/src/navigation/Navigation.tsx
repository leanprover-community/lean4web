import '../css/Modal.css'
import '../css/Navigation.css'

import {
  faArrowRotateRight,
  faCode,
  faEye,
  faHandshake,
  faInfoCircle,
} from '@fortawesome/free-solid-svg-icons'
import {
  faArrowUpRightFromSquare,
  faBars,
  faCloudArrowUp,
  faDownload,
  faGear,
  faHammer,
  faShield,
  faStar,
  faUpload,
  faXmark,
} from '@fortawesome/free-solid-svg-icons'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import ClickAwayListener from '@mui/material/ClickAwayListener'
import Popper from '@mui/material/Popper'
import { useAtom, useAtomValue, useSetAtom } from 'jotai'
import { ChangeEvent, Dispatch, SetStateAction, useState } from 'react'

import { lean4webConfig } from '../../config'
import ZulipIcon from '../assets/zulip.svg'
import { codeAtom } from '../editor/code-atoms'
import ImpressumPopup from '../Popups/Impressum'
import LoadUrlPopup from '../Popups/LoadUrl'
import LoadZulipPopup from '../Popups/LoadZulip'
import PrivacyPopup from '../Popups/PrivacyPolicy'
import ToolsPopup from '../Popups/Tools'
import {
  localOnlySettingsAtom,
  mobileAtom,
  navBarRequestedAtom,
  settingsAtom,
} from '../settings/settings-atoms'
import { lightThemes } from '../settings/settings-types'
import { SettingsPopup } from '../settings/SettingsPopup'
import { setImportUrlAndProjectAtom } from '../store/import-atoms'
import { currentProjectAtom, projectsAtom, visibleProjectsAtom } from '../store/project-atoms'
import { urlArgsStableAtom } from '../store/url-atoms'
import { parseArgs } from '../store/url-converters'
import { save } from '../utils/SaveToFile'
import { Dropdown } from './Dropdown'
import { NavButton } from './NavButton'

const referrerNeedsComparator = (() => {
  // Never highlight comparator option if there's no code
  const args = parseArgs(window.location.hash)
  if (!args.code?.trim() && !args.codez?.trim()) return false // No warning for empty code or example-url-driven code

  // Highlight comparator if there's no referrer or if the referrer isn't safelisted
  if (!document.referrer) return true
  const referrer = new URL(document.referrer)
  if (!lean4webConfig.comparatorSafeList) return true
  return !lean4webConfig.comparatorSafeList.some((item) =>
    item instanceof RegExp ? referrer.hostname.match(item) : referrer.hostname === item,
  )
})()

/** The menu items either appearing inside the dropdown or outside */
function FlexibleMenu({
  isInDropdown = false,
  setOpenNav,
  openExample,
  setOpenExample,
  openLoad,
  setOpenLoad,
  setContent,
  setLoadUrlOpen,
  setLoadZulipOpen,
}: {
  isInDropdown: boolean
  setOpenNav: Dispatch<SetStateAction<boolean>>
  openExample: boolean
  setOpenExample: Dispatch<SetStateAction<boolean>>
  openLoad: boolean
  setOpenLoad: Dispatch<SetStateAction<boolean>>
  setContent: (code: string) => void
  setLoadUrlOpen: Dispatch<SetStateAction<boolean>>
  setLoadZulipOpen: Dispatch<SetStateAction<boolean>>
}) {
  const setImportUrlAndProject = useSetAtom(setImportUrlAndProjectAtom)
  const { data: projects } = useAtomValue(projectsAtom)
  const urlArgs = useAtomValue(urlArgsStableAtom)
  const code = useAtomValue(codeAtom)
  const isUsingUrlCode = !!urlArgs?.url

  const settings = useAtomValue(settingsAtom)
  const themeVariant = lightThemes.includes(settings.theme)
    ? 'light'
    : settings.theme === 'Cobalt'
      ? 'cobalt'
      : 'dark'
  const [localOnlySettings, setLocalOnlySettings] = useAtom(localOnlySettingsAtom)
  const [comparatorWarningDismissed, setComparatorWarningDismissed] = useState(false)
  const comparatorWarningEligible =
    !isInDropdown &&
    !isUsingUrlCode &&
    referrerNeedsComparator &&
    !localOnlySettings.ignoreComparatorWarning
  const [trustButtonEl, setTrustButtonEl] = useState<HTMLAnchorElement | null>(null)
  const [trustArrowEl, setTrustArrowEl] = useState<HTMLElement | null>(null)
  const comparatorWarningOpen =
    !!trustButtonEl && comparatorWarningEligible && !comparatorWarningDismissed

  const loadFileFromDisk = (event: ChangeEvent<HTMLInputElement>) => {
    console.debug('Loading file from disk')
    const fileToLoad = event.target.files![0]
    var fileReader = new FileReader()
    fileReader.onload = (fileLoadedEvent) => {
      var textFromFileLoaded = fileLoadedEvent.target!.result as string
      setContent(textFromFileLoaded)
    }
    fileReader.readAsText(fileToLoad, 'UTF-8')
    // Manually close the menu as we prevent it closing below.
    setOpenLoad(false)
  }

  return (
    <>
      <Dropdown
        open={openExample}
        setOpen={setOpenExample}
        icon={faStar}
        text="Examples"
        useOverlay={isInDropdown}
        onClick={() => {
          setOpenLoad(false)
          !isInDropdown && setOpenNav(false)
        }}
      >
        {projects.map((it) =>
          it.config.examples?.map((example) => (
            <NavButton
              key={`${it.config.name}-${example.name}`}
              icon={faStar}
              text={example.name}
              title={`${it.config.name}: ${example.name}`}
              onClick={() => {
                setImportUrlAndProject({
                  url: `${window.location.origin}/api/example/${it.folder}/${example.file}`,
                  project: it.folder,
                })
                setOpenExample(false)
              }}
            />
          )),
        )}
      </Dropdown>
      <Dropdown
        open={openLoad}
        setOpen={setOpenLoad}
        icon={faUpload}
        text="Load"
        useOverlay={isInDropdown}
        onClick={() => {
          setOpenExample(false)
          !isInDropdown && setOpenNav(false)
        }}
      >
        <input
          id="file-upload"
          type="file"
          onChange={loadFileFromDisk}
          onClick={(ev) => ev.stopPropagation()}
        />
        {/* Need `ev.stopPropagation` to prevent closing until the file is loaded.
          Otherwise the file-upload is destroyed too early. */}
        <label htmlFor="file-upload" className="nav-link" onClick={(ev) => ev.stopPropagation()}>
          <FontAwesomeIcon icon={faUpload} /> Load file from disk
        </label>
        <NavButton
          icon={faCloudArrowUp}
          text="Load from URL"
          onClick={() => {
            setLoadUrlOpen(true)
          }}
        />
        <NavButton
          iconElement={<ZulipIcon />}
          text="Load Zulip Message"
          onClick={() => {
            setLoadZulipOpen(true)
          }}
        />
      </Dropdown>
      {lean4webConfig.comparator && (
        <NavButton
          ref={isInDropdown ? undefined : setTrustButtonEl}
          icon={faHandshake}
          text={'Can I Trust This Proof?'}
          disabled={isUsingUrlCode}
          title={
            isUsingUrlCode
              ? 'Example urls not supported by Comparator tool! Edit the text to enable.'
              : (code ?? '').trim() === ''
                ? 'Open the Comparator verification tool'
                : 'Open this proof in the Comparator verification tool'
          }
          onClick={() => {
            window.location.assign(lean4webConfig.comparator + window.location.hash)
          }}
        />
      )}
      <Popper
        open={comparatorWarningOpen}
        anchorEl={trustButtonEl}
        placement="bottom-end"
        modifiers={[
          { name: 'flip', enabled: false },
          { name: 'offset', options: { offset: [0, 12] } },
          { name: 'arrow', enabled: true, options: { element: trustArrowEl, padding: 8 } },
        ]}
      >
        <ClickAwayListener onClickAway={() => setComparatorWarningDismissed(true)}>
          <div
            className={`comparator-warning ${themeVariant}`}
            role="status"
            aria-label="Verify untrusted proofs with Comparator"
          >
            <span className="comparator-warning-arrow" ref={setTrustArrowEl}></span>
            <button
              className="codicon codicon-close comparator-warning-close"
              aria-label="Dismiss"
              onClick={() => setComparatorWarningDismissed(true)}
            />
            <p>
              Don't trust proofs from untrusted sources unless they're validated against a trusted
              challenge. Use the <strong>Can I Trust This Proof?</strong> button to check this proof
              with the online version of Lean's Comparator tool.
            </p>
            <button
              className="comparator-warning-perma-dismiss"
              onClick={() => {
                setComparatorWarningDismissed(true)
                setLocalOnlySettings('ignoreComparatorWarning', true)
              }}
            >
              Don't show this again
            </button>
          </div>
        </ClickAwayListener>
      </Popper>{' '}
    </>
  )
}

/** The Navigation menu */
export function Menu({
  setContent,
  restart,
  codeMirror,
  setCodeMirror,
}: {
  setContent: (code: string) => void
  restart?: () => void
  codeMirror: boolean
  setCodeMirror: Dispatch<SetStateAction<boolean>>
}) {
  const [visibleProjects] = useAtom(visibleProjectsAtom)
  const [project, setProject] = useAtom(currentProjectAtom)
  const [code] = useAtom(codeAtom)

  // state for handling the dropdown menus
  const [openNav, setOpenNav] = useState(false)
  const [openExample, setOpenExample] = useState(false)
  const [openLoad, setOpenLoad] = useState(false)
  const [loadUrlOpen, setLoadUrlOpen] = useState(false)
  const [loadZulipOpen, setLoadZulipOpen] = useState(false)

  // state for the popups
  const [privacyOpen, setPrivacyOpen] = useState(false)
  const [impressumOpen, setImpressumOpen] = useState(false)
  const [toolsOpen, setToolsOpen] = useState(false)
  const [settingsOpen, setSettingsOpen] = useState(false)

  const [mobile] = useAtom(mobileAtom)

  const hasImpressum = lean4webConfig.impressum || lean4webConfig.contactDetails
  const navBarRequested = useAtomValue(navBarRequestedAtom)
  const [localOnlySettings, setLocalOnlySettings] = useAtom(localOnlySettingsAtom)

  return (
    <div className="menu">
      {project && (
        <select
          name="leanVersion"
          value={project.folder}
          onChange={(ev) => {
            setProject(ev.target.value)
            console.log(`set Lean project to: ${ev.target.value}`)
          }}
        >
          {project.folder}
          {visibleProjects.map((proj) => (
            <option key={proj.folder} value={proj.folder}>
              {proj.config.name}
            </option>
          ))}
        </select>
      )}
      {mobile && (
        <NavButton
          icon={faCode}
          text={codeMirror ? 'Lean' : 'Text'}
          onClick={() => {
            setCodeMirror(!codeMirror)
          }}
        />
      )}
      {!mobile && (
        <FlexibleMenu
          isInDropdown={false}
          setOpenNav={setOpenNav}
          openExample={openExample}
          setOpenExample={setOpenExample}
          openLoad={openLoad}
          setOpenLoad={setOpenLoad}
          setContent={setContent}
          setLoadUrlOpen={setLoadUrlOpen}
          setLoadZulipOpen={setLoadZulipOpen}
        />
      )}
      <Dropdown
        open={openNav}
        setOpen={setOpenNav}
        icon={openNav ? faXmark : faBars}
        onClick={() => {
          setOpenExample(false)
          setOpenLoad(false)
        }}
      >
        {mobile && (
          <FlexibleMenu
            isInDropdown={true}
            setOpenNav={setOpenNav}
            openExample={openExample}
            setOpenExample={setOpenExample}
            openLoad={openLoad}
            setOpenLoad={setOpenLoad}
            setContent={setContent}
            setLoadUrlOpen={setLoadUrlOpen}
            setLoadZulipOpen={setLoadZulipOpen}
          />
        )}
        <NavButton
          icon={faGear}
          text="Settings"
          onClick={() => {
            setSettingsOpen(true)
          }}
        />
        <NavButton icon={faHammer} text="Lean Info" onClick={() => setToolsOpen(true)} />
        {navBarRequested !== null && (
          <NavButton
            icon={faEye}
            text={`${localOnlySettings.hideNavbar ? 'Show' : 'Hide'} site navigation`}
            onClick={() => setLocalOnlySettings('hideNavbar', !localOnlySettings.hideNavbar)}
          />
        )}
        <NavButton icon={faArrowRotateRight} text="Restart server" onClick={restart} />
        <NavButton
          icon={faDownload}
          text="Save file"
          onClick={() => {
            if (code !== undefined) save(code)
          }}
        />
        {hasImpressum && (
          <NavButton
            icon={faInfoCircle}
            text={'Impressum'}
            onClick={() => {
              setImpressumOpen(true)
            }}
          />
        )}
        <NavButton
          icon={faArrowUpRightFromSquare}
          text="Lean community"
          href="https://leanprover-community.github.io/"
        />
        <NavButton icon={faArrowUpRightFromSquare} text="Lean FRO" href="https://lean-lang.org" />
        <NavButton
          icon={faArrowUpRightFromSquare}
          text="GitHub"
          href="https://github.com/leanprover-community/lean4web"
        />

        <NavButton icon={faShield} text="Privacy policy" href="https://lean-lang.org/privacy/" />
        <NavButton icon={faShield} text="Terms of use" href="https://lean-lang.org/terms/" />
      </Dropdown>
      <PrivacyPopup open={privacyOpen} handleClose={() => setPrivacyOpen(false)} />
      {hasImpressum && (
        <ImpressumPopup open={impressumOpen} handleClose={() => setImpressumOpen(false)} />
      )}
      {project && (
        <ToolsPopup
          open={toolsOpen}
          handleClose={() => setToolsOpen(false)}
          project={project.folder}
        />
      )}
      <SettingsPopup
        open={settingsOpen}
        handleClose={() => setSettingsOpen(false)}
        closeNav={() => setOpenNav(false)}
      />
      <LoadUrlPopup open={loadUrlOpen} handleClose={() => setLoadUrlOpen(false)} />
      <LoadZulipPopup
        open={loadZulipOpen}
        handleClose={() => setLoadZulipOpen(false)}
        setContent={setContent}
      />
    </div>
  )
}
