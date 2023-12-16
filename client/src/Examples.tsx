import * as React from 'react'
import { faStar } from '@fortawesome/free-solid-svg-icons';
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome';

const Examples: React.FC<{loadFromUrl:(url: string, project?: string|null) => void, openSubmenu: (ev: React.MouseEvent, component: React.JSX.Element) => void, closeNav: any}> = ({loadFromUrl, openSubmenu, closeNav}) => {

  const load = (file, project=null) => {
    loadFromUrl(`${window.location.origin}/examples/${file}`, project)
    closeNav()
  }

  const exampleMenu = <>
    <span className="nav-link" onClick={() => load("logic.lean", "MathlibLatest")}>Logic</span>
    <span className="nav-link" onClick={() => load("bijection.lean", "MathlibLatest")}>Bijections</span>
    <span className="nav-link" onClick={() => load("rational.lean", "MathlibLatest")}>Rational numbers</span>
    <span className="nav-link" onClick={() => load("ring.lean", "MathlibLatest")}>Commutative rings</span>
    <span className="nav-link" onClick={() => {loadFromUrl("https://raw.githubusercontent.com/JOSHCLUNE/DuperDemo/main/DuperDemo.lean", "DuperDemo"); closeNav()}}>Duper</span>
  </>

  return <span className="nav-link" onClick={(ev) => {openSubmenu(ev, exampleMenu)}}>
    <FontAwesomeIcon icon={faStar} /> Examples
  </span>
}

export default Examples
