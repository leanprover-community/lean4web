import { IconDefinition } from '@fortawesome/free-solid-svg-icons'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { JSX, RefObject } from 'react'

/** A button to appear in the hamburger menu or to navigation bar. */
export function NavButton({
  icon,
  iconElement,
  text,
  href,
  ref,
  ...props
}: {
  icon?: IconDefinition
  iconElement?: JSX.Element
  text: string
  href?: string
  ref?: RefObject<HTMLButtonElement | null>
} & React.AnchorHTMLAttributes<HTMLElement>) {
  if (href)
    return (
      <a
        {...props}
        href={href}
        className={props.className ? `nav-link ${props.className}` : 'nav-link'}
        target="_blank"
        rel="noopener"
      >
        {iconElement ?? <FontAwesomeIcon icon={icon!} />}&nbsp;
        <span>{text}</span>
      </a>
    )
  return (
    <button
      {...props}
      ref={ref}
      type={undefined}
      className={props.className ? `nav-link ${props.className}` : 'nav-link'}
    >
      {iconElement ?? <FontAwesomeIcon icon={icon!} />}&nbsp;<span>{text}</span>
    </button>
  )
}
