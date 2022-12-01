import { faStar } from '@fortawesome/free-solid-svg-icons';
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome';
import * as React from 'react'
import { useEffect, useState, useRef } from 'react';

const Examples: React.FC<{loadFromUrl:(url: string) => void}> = ({loadFromUrl}) => {
  const [open, setOpen] = useState(false);
  const componentRef = useRef<HTMLElement>();

  useEffect(() => {
   document.body.addEventListener("click", (ev) => {
    if (componentRef.current && !componentRef.current.contains(ev.target as HTMLElement)) {
      setOpen(false)
    }
   })
  }, [])

  const load = (file) => {
    loadFromUrl(`/examples/${file}`)
    setOpen(false)
  }

  return (
    <span style={{position:"relative"}} ref={componentRef}>
      <span className="nav-link" onClick={() => setOpen(!open)}>
        <FontAwesomeIcon icon={faStar} /> Examples
      </span>
      {open?
        <div className="dropdown-menu">
        <p className="nav-link" onClick={() => load("logic.lean")}>Logic</p>
        <p className="nav-link" onClick={() => load("bijection.lean")}>Bijections</p>
        <p className="nav-link" onClick={() => load("rational.lean")}>Rational numbers</p>
        <p className="nav-link" onClick={() => load("ring.lean")}>Commutative rings</p>
        </div> : null}
    </span>
  )
}

export default Examples
