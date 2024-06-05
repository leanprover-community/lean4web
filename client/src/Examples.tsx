import * as React from 'react'
import { faStar } from '@fortawesome/free-solid-svg-icons';
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome';
import lean4webConfig from './config/config'

const Examples: React.FC<{loadFromUrl:(url: string, project?: string|null) => void, openSubmenu: (ev: React.MouseEvent, component: React.JSX.Element) => void, closeNav: any}> = ({loadFromUrl, openSubmenu, closeNav}) => {

  const load = (file, project=null) => {
    loadFromUrl(`${window.location.origin}/examples/${file}`, project)
    closeNav()
  }

  const exampleMenu = <>
    {lean4webConfig.projects.map(proj => proj.examples?.map(example =>
      <span key={`${proj.name}-${example.name}`} className="nav-link" onClick={() => load(`${proj.folder}/${example.file}`, proj.folder)}>{example.name}</span>

    ))}
  </>

  return <span className="nav-link" onClick={(ev) => {openSubmenu(ev, exampleMenu)}}>
    <FontAwesomeIcon icon={faStar} /> Examples
  </span>
}

export default Examples
