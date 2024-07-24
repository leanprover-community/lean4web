import { useState } from 'react'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { IconDefinition } from '@fortawesome/free-solid-svg-icons'
import ZulipIcon from './assets/zulip.svg'
import { faArrowRotateRight, faArrowUpRightFromSquare, faDownload, faBars, faXmark, faShield, faHammer, faGear, faStar, faUpload, faCloudArrowUp } from '@fortawesome/free-solid-svg-icons'
import { saveAs } from 'file-saver'

import SettingsPopup from './Popups/Settings'
import PrivacyPopup from './Popups/PrivacyPolicy';
import ToolsPopup from './Popups/Tools';
import LoadUrlPopup from './Popups/LoadUrl';
import LoadZulipPopup from './Popups/LoadZulip';

import lean4webConfig from './config/config'
import './css/Modal.css'
import './css/Navigation.css'

/** A button to appear in the hamburger menu or to navigation bar. */
export const NavButton: React.FC<{
  icon?: IconDefinition
  iconElement?: JSX.Element
  text: string
  onClick?: React.MouseEventHandler<HTMLAnchorElement>
  href?: string
}> = ({icon, iconElement, text, onClick=()=>{}, href=null}) => {
  // note: it seems that we can just leave the `target="_blank"` and it has no
  // effect on links without a `href`. If not, add `if (href)` statement here...
  return <a className="nav-link" onClick={onClick} href={href!} target="_blank">
    {iconElement ?? <FontAwesomeIcon icon={icon!} />}&nbsp;{text}
  </a>
}

/** A button to appear in the hamburger menu or to navigation bar. */
export const Dropdown: React.FC<{
  open: boolean
  setOpen: React.Dispatch<React.SetStateAction<boolean>>
  icon?: IconDefinition
  text?: string
  useOverlay?: boolean
  onClick?: React.MouseEventHandler<HTMLAnchorElement>
  children?: React.ReactNode
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
export const Popup: React.FC<{
  open: boolean
  handleClose: () => void // TODO: what's the correct type?
  children?: React.ReactNode
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
const FlexibleMenu: React.FC <{
  isInDropdown: boolean,
  setOpenNav: any,
  openExample: any,
  setOpenExample: any,
  openLoad: any,
  setOpenLoad: any,
  loadFromUrl: any,
  setCode: any,
}> = ({isInDropdown = false, setOpenNav, openExample, setOpenExample, openLoad,
  setOpenLoad, loadFromUrl, setCode
}) => {

  const [loadUrlOpen, setLoadUrlOpen] = useState(false)
  const [loadZulipOpen, setLoadZulipOpen] = useState(false)

  const loadFileFromDisk = (event: React.ChangeEvent<HTMLInputElement>) => {
    const fileToLoad = event.target.files![0]
    var fileReader = new FileReader();
    fileReader.onload = (fileLoadedEvent) => {
        var textFromFileLoaded = fileLoadedEvent.target!.result as string;
        // setContent(textFromFileLoaded)
    }
    fileReader.readAsText(fileToLoad, "UTF-8")
    setOpenNav(false)
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
            loadFromUrl(`${window.location.origin}/examples/${proj.folder}/${example.file}`, proj.folder);
            setOpenExample(false)
          }} />
      ))}
    </Dropdown>
    <Dropdown open={openLoad} setOpen={setOpenLoad} icon={faUpload} text="Load"
        useOverlay={isInDropdown}
        onClick={() => {setOpenExample(false); (!isInDropdown && setOpenNav(false))}}>
      <label htmlFor="file-upload" className="nav-link" >
        
        <FontAwesomeIcon icon={faUpload} /> Load file from disk
      </label>
      <NavButton icon={faCloudArrowUp} text="Load from URL" onClick={() => {setLoadUrlOpen(true)}} />
      <NavButton iconElement={<ZulipIcon />} text="Load Zulip Message" onClick={() => {setLoadZulipOpen(true)}} />
      <input id="file-upload" type="file" onChange={loadFileFromDisk} />
    </Dropdown>
    {/* {restart && <NavButton icon={faArrowRotateRight} text="Restart server" onClick={restart} />} */}
    <LoadUrlPopup open={loadUrlOpen} handleClose={() => setLoadUrlOpen(false)} loadFromUrl={loadFromUrl} />
    <LoadZulipPopup open={loadZulipOpen} handleClose={() => setLoadZulipOpen(false)} setCode={setCode} />
  </>
}

/** The Navigation menu */
export const Menu: React.FC <{
  code: string,
  setCode: any,
  project: any,
  setProject: any,
  theme: any,
  setTheme: any,
  setUrl: any,
  contentFromUrl: any,
  settings: any,
}> = ({code, setCode, project, setProject, theme, setTheme, setUrl, contentFromUrl, settings}) => {
  // state for handling the dropdown menus
  const [openNav, setOpenNav] = useState(false)
  const [openExample, setOpenExample] = useState(false)
  const [openLoad, setOpenLoad] = useState(false)

  // state for the popups
  const [privacyOpen, setPrivacyOpen] = useState(false)
  const [toolsOpen, setToolsOpen] = useState(false)
  const [settingsOpen, setSettingsOpen] = useState(false)

  const loadFromUrl = (url: string, project:string|undefined=undefined) => {
    console.debug('load code from url')
    setUrl((oldUrl: string) => {
      if (oldUrl === url) {
        setCode(contentFromUrl)
      }
      return url
    })
    if (project) {
      setProject(project)
    }
  }

  return  <div className='menu'>
    { !settings.verticalLayout &&
      <FlexibleMenu isInDropdown={false}
        setOpenNav={setOpenNav}
        openExample={openExample}
        setOpenExample={setOpenExample}
        openLoad={openLoad}
        setOpenLoad={setOpenLoad}
        loadFromUrl={loadFromUrl}
        setCode={setCode} />
    }
    <Dropdown open={openNav} setOpen={setOpenNav} icon={openNav ? faXmark : faBars} onClick={() => {setOpenExample(false); setOpenLoad(false)}}>
      { settings.verticalLayout &&
        <FlexibleMenu isInDropdown={true}
          setOpenNav={setOpenNav}
          openExample={openExample}
          setOpenExample={setOpenExample}
          openLoad={openLoad}
          setOpenLoad={setOpenLoad}
          loadFromUrl={loadFromUrl}
          setCode={setCode} />
      }
      <NavButton icon={faGear} text="Settings" onClick={() => {setSettingsOpen(true)}} />
      <NavButton icon={faHammer} text="Tools: Version" onClick={() => setToolsOpen(true)} />
      <NavButton icon={faDownload} text="Save file" onClick={() => save(code)} />
      <NavButton icon={faShield} text={'Privacy policy'} onClick={() => {setPrivacyOpen(true)}} />
      <NavButton icon={faArrowUpRightFromSquare} text="Lean community" href="https://leanprover-community.github.io/" />
      <NavButton icon={faArrowUpRightFromSquare} text="Lean documentation" href="https://leanprover.github.io/lean4/doc/" />
      <NavButton icon={faArrowUpRightFromSquare} text="GitHub" href="https://github.com/hhu-adam/lean4web" />
    </Dropdown>
    <PrivacyPopup open={privacyOpen} handleClose={() => setPrivacyOpen(false)} />
    <ToolsPopup open={toolsOpen} handleClose={() => setToolsOpen(false)} />
    <SettingsPopup open={settingsOpen} handleClose={() => setSettingsOpen(false)} closeNav={() => setOpenNav(false)}
      theme={theme} setTheme={setTheme} project={project} setProject={setProject} />
  </div>
}
