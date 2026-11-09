import { IconDefinition } from '@fortawesome/free-solid-svg-icons'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { JSX, Ref } from 'react'

/** A button to appear in the hamburger menu or to navigation bar. */
export function NavButton({
  icon,
  iconElement,
  text,
  disabled = false,
  href,
  ref,
  ...props
}: {
  icon?: IconDefinition
  iconElement?: JSX.Element
  text: string
  disabled?: boolean
  href?: string
  ref?: Ref<HTMLButtonElement>
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
      className={`nav-link${disabled ? ' disabled' : ''} ${props.className ?? ''}`}
      type={undefined}
      aria-disabled={disabled || undefined}
      onClick={disabled ? (e) => e.preventDefault() : props.onClick}
    >
      {iconElement ?? <FontAwesomeIcon icon={icon!} />}&nbsp;<span>{text}</span>
    </button>
  )
}
