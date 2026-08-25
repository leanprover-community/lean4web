import '../css/Modal.css'
import '../css/Navigation.css'

import {
  faArrowRotateRight,
  faCode,
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
import { useAtom } from 'jotai'
import {
  ChangeEvent,
  Dispatch,
  RefObject,
  SetStateAction,
  useRef,
  useState,
} from 'react'

import { lean4webConfig } from '../../config'
import ZulipIcon from '../assets/zulip.svg'
import { codeAtom } from '../editor/code-atoms'
import ImpressumPopup from '../Popups/Impressum'
import JoinCollaborationPopup from '../Popups/JoinCollaboration'
import LoadUrlPopup from '../Popups/LoadUrl'
import LoadZulipPopup from '../Popups/LoadZulip'
import PrivacyPopup from '../Popups/PrivacyPolicy'
import ToolsPopup from '../Popups/Tools'
import { mobileAtom } from '../settings/settings-atoms'
import { SettingsPopup } from '../settings/SettingsPopup'
import { isCollaboratingAtom } from '../store/collaboration-atoms'
import { setImportUrlAndProjectAtom } from '../store/import-atoms'
import {
  currentProjectAtom,
  projectsAtom,
  visibleProjectsAtom,
} from '../store/project-atoms'
import { save } from '../utils/SaveToFile'
import { Dropdown } from './Dropdown'
import { NavButton } from './NavButton'
import RotatingGlobe from './RotatingGlobe'

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
  setJoinCollabOpen,
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
  setJoinCollabOpen: Dispatch<SetStateAction<boolean>>
}) {
  const ENABLE_COLLAB = import.meta.env.VITE_COLLAB != 'false'
  const [isCollaborating] = useAtom(isCollaboratingAtom)
  const [, setImportUrlAndProject] = useAtom(setImportUrlAndProjectAtom)
  const [{ data: projects }] = useAtom(projectsAtom)
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

  const ref = useRef<HTMLInputElement>(null)

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
          if (!isInDropdown) setOpenNav(false)
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
                setOpenNav(false)
              }}
            />
          )),
        )}
      </Dropdown>
      <input
        ref={ref}
        id="file-upload"
        type="file"
        onChange={loadFileFromDisk}
      />
      <Dropdown
        open={openLoad}
        setOpen={setOpenLoad}
        icon={faUpload}
        text="Load"
        useOverlay={isInDropdown}
        onClick={() => {
          setOpenExample(false)
          if (!isInDropdown) setOpenNav(false)
        }}
      >
        <button
          type="button"
          className="nav-link"
          onClick={() => ref.current?.click()}
        >
          <FontAwesomeIcon icon={faUpload} aria-hidden="true" />
          Load file from disk
        </button>
        <NavButton
          icon={faCloudArrowUp}
          text="Load from URL"
          onClick={() => {
            setLoadUrlOpen(true)
            setOpenNav(false)
          }}
        />
        <NavButton
          iconElement={<ZulipIcon />}
          text="Load Zulip Message"
          onClick={() => {
            setLoadZulipOpen(true)
            setOpenNav(false)
          }}
        />
      </Dropdown>
      {ENABLE_COLLAB && !isCollaborating && (
        <NavButton
          iconElement={<RotatingGlobe />}
          text="Collaborate"
          onClick={() => {
            setJoinCollabOpen(true)
            setOpenNav(false)
          }}
        />
      )}
    </>
  )
}

/** The Navigation menu */
export function Menu({
  setContent,
  restart,
  codeMirror,
  setCodeMirror,
  handleJoinCollab,
  firstItemRef,
}: {
  setContent: (code: string) => void
  restart?: () => void
  codeMirror: boolean
  setCodeMirror: Dispatch<SetStateAction<boolean>>
  handleJoinCollab: () => void
  firstItemRef?: RefObject<HTMLSelectElement | null>
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
  const [joinCollabOpen, setJoinCollabOpen] = useState(false)

  // state for the popups
  const [privacyOpen, setPrivacyOpen] = useState(false)
  const [impressumOpen, setImpressumOpen] = useState(false)
  const [toolsOpen, setToolsOpen] = useState(false)
  const [settingsOpen, setSettingsOpen] = useState(false)

  const [mobile] = useAtom(mobileAtom)

  const hasImpressum = lean4webConfig.impressum || lean4webConfig.contactDetails

  return (
    <>
      {project && (
        <select
          ref={firstItemRef}
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
          setJoinCollabOpen={setJoinCollabOpen}
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
            setJoinCollabOpen={setJoinCollabOpen}
          />
        )}
        <NavButton
          icon={faGear}
          text="Settings"
          onClick={() => {
            setSettingsOpen(true)
            setOpenNav(false)
          }}
        />
        <NavButton
          icon={faHammer}
          text="Lean Info"
          onClick={() => {
            setToolsOpen(true)
            setOpenNav(false)
          }}
        />
        <NavButton
          icon={faArrowRotateRight}
          text="Restart server"
          onClick={() => {
            restart?.()
            setOpenNav(false)
          }}
        />
        <NavButton
          icon={faDownload}
          text="Save"
          onClick={() => {
            if (code !== undefined) save(code, project?.folder)
            setOpenNav(false)
          }}
        />
        <NavButton
          icon={faShield}
          text={'Privacy policy'}
          onClick={() => {
            setPrivacyOpen(true)
            setOpenNav(false)
          }}
        />
        {hasImpressum && (
          <NavButton
            icon={faInfoCircle}
            text={'Impressum'}
            onClick={() => {
              setImpressumOpen(true)
              setOpenNav(false)
            }}
          />
        )}
        <NavButton
          icon={faArrowUpRightFromSquare}
          text="Lean community"
          href="https://leanprover-community.github.io/"
          onClick={() => {
            setOpenNav(false)
          }}
        />
        <NavButton
          icon={faArrowUpRightFromSquare}
          text="Lean FRO"
          href="https://lean-lang.org"
          onClick={() => {
            setOpenNav(false)
          }}
        />
        <NavButton
          icon={faArrowUpRightFromSquare}
          text="GitHub"
          href="https://github.com/leanprover-community/lean4web"
          onClick={() => {
            setOpenNav(false)
          }}
        />
      </Dropdown>
      <PrivacyPopup
        open={privacyOpen}
        handleClose={() => setPrivacyOpen(false)}
      />
      {hasImpressum && (
        <ImpressumPopup
          open={impressumOpen}
          handleClose={() => setImpressumOpen(false)}
        />
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
      <LoadUrlPopup
        open={loadUrlOpen}
        handleClose={() => setLoadUrlOpen(false)}
      />
      <LoadZulipPopup
        open={loadZulipOpen}
        handleClose={() => setLoadZulipOpen(false)}
        setContent={setContent}
      />
      <JoinCollaborationPopup
        open={joinCollabOpen}
        handleJoinCollab={handleJoinCollab}
        handleClose={() => {
          setJoinCollabOpen(false)
        }}
      />
    </>
  )
}
