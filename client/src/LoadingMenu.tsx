import { faUpload } from '@fortawesome/free-solid-svg-icons';
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome';
import * as React from 'react'
import { useEffect } from 'react';
import { LoadUrl, LoadZulipMessage } from './LoadUrl';

const LoadingMenu: React.FC<{loadFromUrl: (url: string) => void, setContent: (url: string) => void, openSubmenu: (ev: React.MouseEvent, component: React.JSX.Element) => void, closeNav: any}> = ({loadFromUrl, setContent, openSubmenu, closeNav}) => {

  const loadFileFromDisk = (event) => {
    const fileToLoad = event.target.files[0]
    var fileReader = new FileReader();
    fileReader.onload = (fileLoadedEvent) => {
        var textFromFileLoaded = fileLoadedEvent.target.result as string;
        setContent(textFromFileLoaded)
    }
    fileReader.readAsText(fileToLoad, "UTF-8")
    closeNav()
  }

  const submenu = <>
    <label htmlFor="file-upload" className="nav-link" >
      <FontAwesomeIcon icon={faUpload} /> Load file from disk
    </label>
    <LoadUrl loadFromUrl={loadFromUrl} closeNav={closeNav} />
    <LoadZulipMessage setContent={setContent} closeNav={closeNav} />
    <input id="file-upload" type="file" onChange={loadFileFromDisk} />
  </>

  return <span className="nav-link" onClick={(ev) => openSubmenu(ev, submenu)}>
    <FontAwesomeIcon icon={faUpload} /> Load
  </span>
}

export default LoadingMenu
