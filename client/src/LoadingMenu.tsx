import { faUpload } from '@fortawesome/free-solid-svg-icons';
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome';
import * as React from 'react'
import { useEffect } from 'react';
import { LoadUrl, LoadZulipMessage } from './LoadUrl';

const LoadingMenu: React.FC<{loadFromUrl: (url: string) => void, setContent: (url: string) => void, openSubmenu: (ev: React.MouseEvent, component: React.JSX.Element) => void}> = ({loadFromUrl, setContent, openSubmenu}) => {

  const loadFileFromDisk = (event) => {
    const fileToLoad = event.target.files[0]
    var fileReader = new FileReader();
    fileReader.onload = (fileLoadedEvent) => {
        var textFromFileLoaded = fileLoadedEvent.target.result as string;
        setContent(textFromFileLoaded)
    }
    fileReader.readAsText(fileToLoad, "UTF-8")
  }

  const submenu = <>
    <label htmlFor="file-upload" className="nav-link" >
      <FontAwesomeIcon icon={faUpload} /> Load file from disk
    </label>
    <LoadUrl loadFromUrl={loadFromUrl} />
    <LoadZulipMessage loadZulipMessage={loadFromUrl} />
    <input id="file-upload" type="file" onChange={loadFileFromDisk} />
  </>

  return <span className="nav-link" onClick={(ev) => openSubmenu(ev, submenu)}>
    <FontAwesomeIcon icon={faUpload} /> Load
  </span>
}

export default LoadingMenu
