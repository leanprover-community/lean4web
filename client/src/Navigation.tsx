import { ChangeEvent, Dispatch, FC, MouseEventHandler, ReactNode, SetStateAction, useContext, useState } from 'react'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { IconDefinition, faArrowRotateRight, faCode } from '@fortawesome/free-solid-svg-icons'
import ZulipIcon from './assets/zulip.svg'
import { faArrowUpRightFromSquare, faDownload, faBars, faXmark, faShield, faHammer, faGear, faStar, faUpload, faCloudArrowUp } from '@fortawesome/free-solid-svg-icons'
import { saveAs } from 'file-saver'

import SettingsPopup, { PreferencesContext } from './Popups/Settings'
import PrivacyPopup from './Popups/PrivacyPolicy';
import ToolsPopup from './Popups/Tools';
import LoadUrlPopup from './Popups/LoadUrl';
import LoadZulipPopup from './Popups/LoadZulip';

import lean4webConfig from './config/config'
import './css/Modal.css'
import './css/Navigation.css'

/** A button to appear in the hamburger menu or to navigation bar. */
export const NavButton: FC<{
  icon?: IconDefinition
  iconElement?: JSX.Element
  text: string
  onClick?: MouseEventHandler<HTMLAnchorElement>
  href?: string
}> = ({icon, iconElement, text, onClick=()=>{}, href=null}) => {
  // note: it seems that we can just leave the `target="_blank"` and it has no
  // effect on links without a `href`. If not, add `if (href)` statement here...
  return <a className="nav-link" onClick={onClick} href={href!} target="_blank">
    {iconElement ?? <FontAwesomeIcon icon={icon!} />}&nbsp;{text}
  </a>
}

/** A button to appear in the hamburger menu or to navigation bar. */
export const Dropdown: FC<{
  open: boolean
  setOpen: Dispatch<SetStateAction<boolean>>
  icon?: IconDefinition
  text?: string
  useOverlay?: boolean
  onClick?: MouseEventHandler<HTMLAnchorElement>
  children?: ReactNode
}> = ({open, setOpen, icon, text, useOverlay=false, onClick, children}) => {
  return <><div className='dropdown'>
    <NavButton icon={icon} text={text!} onClick={(ev) => {setOpen(!open); onClick!(ev); ev.stopPropagation()}} />
    {open &&
      <div className={`dropdown-content${open?'': ' '}`} onClick={() => setOpen(false)}>
        {children}
      </div>
    }
  </div>
    { useOverlay && open &&
     <div className="dropdown-overlay" onClick={(ev) => {setOpen(false); ev.stopPropagation()}}/>
    }
  </>
}

/** A popup which overlays the entire screen. */
export const Popup: FC<{
  open: boolean
  handleClose: () => void // TODO: what's the correct type?
  children?: ReactNode
}> = ({open, handleClose, children}) => {
  return <div className={`modal-wrapper${open? '': ' hidden'}`}>
    <div className="modal-backdrop" onClick={handleClose} />
      <div className="modal">
        <div className="codicon codicon-close modal-close" onClick={handleClose}></div>
        {children}
      </div>
    </div>
}

const save = (content: string) => {
  var blob = new Blob([content], {type: "text/plain;charset=utf-8"});
  saveAs(blob, "Lean4WebDownload.lean");
}

/** The menu items either appearing inside the dropdown or outside */
const FlexibleMenu: FC <{
  isInDropdown: boolean,
  setOpenNav: Dispatch<SetStateAction<boolean>>,
  openExample: boolean,
  setOpenExample: Dispatch<SetStateAction<boolean>>,
  openLoad: boolean,
  setOpenLoad: Dispatch<SetStateAction<boolean>>,
  loadFromUrl: (url: string, project?: string | undefined) => void,
  setContent: (code: string) => void,
  setLoadUrlOpen: Dispatch<SetStateAction<boolean>>,
  setLoadZulipOpen: Dispatch<SetStateAction<boolean>>
}> = ({isInDropdown = false, setOpenNav, openExample, setOpenExample, openLoad,
  setOpenLoad, loadFromUrl, setContent, setLoadUrlOpen, setLoadZulipOpen
}) => {

  const loadFileFromDisk = (event: ChangeEvent<HTMLInputElement>) => {
    console.debug('Loading file from disk')
    const fileToLoad = event.target.files![0]
    var fileReader = new FileReader();
    fileReader.onload = (fileLoadedEvent) => {
        var textFromFileLoaded = fileLoadedEvent.target!.result as string;
        setContent(textFromFileLoaded)
    }
    fileReader.readAsText(fileToLoad, "UTF-8")
    // Manually close the menu as we prevent it closing below.
    setOpenLoad(false)
  }

  return <>
    <Dropdown open={openExample} setOpen={setOpenExample} icon={faStar} text="Examples"
        useOverlay={isInDropdown}
        onClick={() => {setOpenLoad(false); (!isInDropdown && setOpenNav(false))}}>
      {lean4webConfig.projects.map(proj => proj.examples?.map(example =>
        <NavButton
          key={`${proj.name}-${example.name}`}
          icon={faStar} text={example.name}
          onClick={() => {
            loadFromUrl(`${window.location.origin}/api/examples/${proj.folder}/${example.file}`, proj.folder);
            setOpenExample(false)
          }} />
      ))}
    </Dropdown>
    <Dropdown open={openLoad} setOpen={setOpenLoad} icon={faUpload} text="Load"
        useOverlay={isInDropdown}
        onClick={() => {setOpenExample(false); (!isInDropdown && setOpenNav(false))}}>
      <input id="file-upload" type="file" onChange={loadFileFromDisk} onClick={(ev) => ev.stopPropagation()} />
      {/* Need `ev.stopPropagation` to prevent closing until the file is loaded.
          Otherwise the file-upload is destroyed too early. */}
      <label htmlFor="file-upload" className="nav-link" onClick={(ev) => ev.stopPropagation()} >
        <FontAwesomeIcon icon={faUpload} /> Load file from disk
      </label>
      <NavButton icon={faCloudArrowUp} text="Load from URL" onClick={() => {setLoadUrlOpen(true)}} />
      <NavButton iconElement={<ZulipIcon />} text="Load Zulip Message" onClick={() => {setLoadZulipOpen(true)}} />
    </Dropdown>
  </>
}

/** The Navigation menu */
export const Menu: FC <{
  code: string,
  setContent: (code: string) => void,
  project: string,
  setProject: Dispatch<SetStateAction<string>>,
  setUrl: Dispatch<SetStateAction<string | null>>,
  codeFromUrl: string,
  restart: () => void,
  codeMirror: boolean,
  setCodeMirror: Dispatch<SetStateAction<boolean>>,
}> = ({code, setContent, project, setProject, setUrl, codeFromUrl, restart, codeMirror, setCodeMirror}) => {
  // state for handling the dropdown menus
  const [openNav, setOpenNav] = useState(false)
  const [openExample, setOpenExample] = useState(false)
  const [openLoad, setOpenLoad] = useState(false)
  const [loadUrlOpen, setLoadUrlOpen] = useState(false)
  const [loadZulipOpen, setLoadZulipOpen] = useState(false)

  // state for the popups
  const [privacyOpen, setPrivacyOpen] = useState(false)
  const [toolsOpen, setToolsOpen] = useState(false)
  const [settingsOpen, setSettingsOpen] = useState(false)

  const { preferences } = useContext(PreferencesContext)

  const loadFromUrl = (url: string, project:string|undefined=undefined) => {
    console.debug('load code from url')
    setUrl((oldUrl: string|null) => {
      if (oldUrl === url) {
        setContent(codeFromUrl)
      }
      return url
    })
    if (project) {
      setProject(project)
    }
  }

  return  <div className='menu'>
    <select
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
    { preferences.mobile &&
      <NavButton icon={faCode} text={codeMirror ? "Lean" : "Text"} onClick={() => {setCodeMirror(!codeMirror)}}/>
    }
    { !preferences.mobile &&
      <FlexibleMenu isInDropdown={false}
        setOpenNav={setOpenNav}
        openExample={openExample}
        setOpenExample={setOpenExample}
        openLoad={openLoad}
        setOpenLoad={setOpenLoad}
        loadFromUrl={loadFromUrl}
        setContent={setContent}
        setLoadUrlOpen={setLoadUrlOpen}
        setLoadZulipOpen={setLoadZulipOpen} />
    }
    <Dropdown open={openNav} setOpen={setOpenNav} icon={openNav ? faXmark : faBars} onClick={() => {setOpenExample(false); setOpenLoad(false)}}>
      { preferences.mobile &&
        <FlexibleMenu isInDropdown={true}
          setOpenNav={setOpenNav}
          openExample={openExample}
          setOpenExample={setOpenExample}
          openLoad={openLoad}
          setOpenLoad={setOpenLoad}
          loadFromUrl={loadFromUrl}
          setContent={setContent}
          setLoadUrlOpen={setLoadUrlOpen}
          setLoadZulipOpen={setLoadZulipOpen} />
      }
      <NavButton icon={faGear} text="Settings" onClick={() => {setSettingsOpen(true)}} />
      <NavButton icon={faHammer} text="Lean Version Info" onClick={() => setToolsOpen(true)} />
      <NavButton icon={faArrowRotateRight} text="Restart server" onClick={restart} />
      <NavButton icon={faDownload} text="Save file" onClick={() => save(code)} />
      <NavButton icon={faShield} text={'Privacy policy'} onClick={() => {setPrivacyOpen(true)}} />
      <NavButton icon={faArrowUpRightFromSquare} text="Lean community" href="https://leanprover-community.github.io/" />
      <NavButton icon={faArrowUpRightFromSquare} text="Lean documentation" href="https://leanprover.github.io/lean4/doc/" />
      <NavButton icon={faArrowUpRightFromSquare} text="GitHub" href="https://github.com/hhu-adam/lean4web" />
    </Dropdown>
    <PrivacyPopup open={privacyOpen} handleClose={() => setPrivacyOpen(false)} />
    <ToolsPopup open={toolsOpen} handleClose={() => setToolsOpen(false)} project={project} />
    <SettingsPopup open={settingsOpen} handleClose={() => setSettingsOpen(false)} closeNav={() => setOpenNav(false)}
      project={project} setProject={setProject} />
    <LoadUrlPopup open={loadUrlOpen} handleClose={() => setLoadUrlOpen(false)} loadFromUrl={loadFromUrl} />
    <LoadZulipPopup open={loadZulipOpen} handleClose={() => setLoadZulipOpen(false)} setContent={setContent} />
  </div>
}
