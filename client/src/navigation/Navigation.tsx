import '../css/Modal.css'
import '../css/Navigation.css'

import { faArrowRotateRight, faCode, faInfoCircle } from '@fortawesome/free-solid-svg-icons'
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
import { useAtom } from 'jotai'
import { ChangeEvent, Dispatch, SetStateAction, useState } from 'react'

import ZulipIcon from '../assets/zulip.svg'
import lean4webConfig from '../config/config'
import { codeAtom } from '../editor/code-atoms'
import ImpressumPopup from '../Popups/Impressum'
import LoadUrlPopup from '../Popups/LoadUrl'
import LoadZulipPopup from '../Popups/LoadZulip'
import PrivacyPopup from '../Popups/PrivacyPolicy'
import ToolsPopup from '../Popups/Tools'
import { mobileAtom } from '../settings/settings-atoms'
import { SettingsPopup } from '../settings/SettingsPopup'
import { setImportUrlAndProjectAtom } from '../store/import-atoms'
import { projectAtom } from '../store/project-atoms'
import { save } from '../utils/SaveToFile'
import { Dropdown } from './Dropdown'
import { NavButton } from './NavButton'

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
  const [, setImportUrlAndProject] = useAtom(setImportUrlAndProjectAtom)
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
        {lean4webConfig.projects.map((proj) =>
          proj.examples?.map((example) => (
            <NavButton
              key={`${proj.name}-${example.name}`}
              icon={faStar}
              text={example.name}
              onClick={() => {
                setImportUrlAndProject({
                  url: `${window.location.origin}/api/example/${proj.folder}/${example.file}`,
                  project: proj.folder,
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
  const [project, setProject] = useAtom(projectAtom)
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

  return (
    <div className="menu">
      <select
        name="leanVersion"
        value={project}
        onChange={(ev) => {
          setProject(ev.target.value)
          console.log(`set Lean project to: ${ev.target.value}`)
        }}
      >
        {lean4webConfig.projects.map((proj) => (
          <option key={proj.folder} value={proj.folder}>
            {proj.name ?? proj.folder}
          </option>
        ))}
      </select>
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
        <NavButton icon={faArrowRotateRight} text="Restart server" onClick={restart} />
        <NavButton
          icon={faDownload}
          text="Save file"
          onClick={() => {
            if (code !== undefined) save(code)
          }}
        />
        <NavButton
          icon={faShield}
          text={'Privacy policy'}
          onClick={() => {
            setPrivacyOpen(true)
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
        <NavButton
          icon={faArrowUpRightFromSquare}
          text="Lean documentation"
          href="https://leanprover.github.io/lean4/doc/"
        />
        <NavButton
          icon={faArrowUpRightFromSquare}
          text="GitHub"
          href="https://github.com/hhu-adam/lean4web"
        />
      </Dropdown>
      <PrivacyPopup open={privacyOpen} handleClose={() => setPrivacyOpen(false)} />
      {hasImpressum && (
        <ImpressumPopup open={impressumOpen} handleClose={() => setImpressumOpen(false)} />
      )}
      <ToolsPopup open={toolsOpen} handleClose={() => setToolsOpen(false)} project={project} />
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
