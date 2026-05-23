import { IconDefinition } from '@fortawesome/free-solid-svg-icons'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { JSX } from 'react'

/** A button to appear in the hamburger menu or to navigation bar. */
export function NavButton({
  icon,
  iconElement,
  text,
  ...props
}: {
  icon?: IconDefinition
  iconElement?: JSX.Element
  text: string
} & React.AnchorHTMLAttributes<HTMLAnchorElement>) {
  // note: it seems that we can just leave the `target="_blank"` and it has no
  // effect on links without a `href`. If not, add `if (href)` statement here...
  return (
    <a
      {...props}
      className={props.className ? `nav-link ${props.className}` : 'nav-link'}
      target="_blank"
    >
      {iconElement ?? <FontAwesomeIcon icon={icon!} />}&nbsp;<span>{text}</span>
    </a>
  )
}
