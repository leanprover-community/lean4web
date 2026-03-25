import { IconDefinition } from '@fortawesome/free-solid-svg-icons'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { JSX, MouseEventHandler } from 'react'

/** A button to appear in the hamburger menu or to navigation bar. */
export function NavButton({
  icon,
  iconElement,
  text,
  title,
  onClick = () => {},
  href = undefined,
}: {
  icon?: IconDefinition
  iconElement?: JSX.Element
  text: string
  title?: string
  onClick?: MouseEventHandler<HTMLAnchorElement>
  href?: string
}) {
  // note: it seems that we can just leave the `target="_blank"` and it has no
  // effect on links without a `href`. If not, add `if (href)` statement here...
  return (
    <a className="nav-link" title={title} onClick={onClick} href={href!} target="_blank">
      {iconElement ?? <FontAwesomeIcon icon={icon!} />}&nbsp;{text}
    </a>
  )
}
