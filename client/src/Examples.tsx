import * as React from 'react'
import { faStar } from '@fortawesome/free-solid-svg-icons';
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome';

const Examples: React.FC<{loadFromUrl:(url: string) => void, openSubmenu: (ev: React.MouseEvent, component: React.JSX.Element) => void, closeNav: any}> = ({loadFromUrl, openSubmenu, closeNav}) => {

  const load = (file) => {
    loadFromUrl(`${window.location.origin}/examples/${file}`)
    closeNav()
  }

  const exampleMenu = <>
    <span className="nav-link" onClick={() => load("logic.lean")}>Logic</span>
    <span className="nav-link" onClick={() => load("bijection.lean")}>Bijections</span>
    <span className="nav-link" onClick={() => load("rational.lean")}>Rational numbers</span>
    <span className="nav-link" onClick={() => load("ring.lean")}>Commutative rings</span>
  </>

  return <span className="nav-link" onClick={(ev) => {openSubmenu(ev, exampleMenu)}}>
    <FontAwesomeIcon icon={faStar} /> Examples
  </span>
}

export default Examples
