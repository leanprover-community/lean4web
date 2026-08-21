import { IconDefinition } from '@fortawesome/free-solid-svg-icons'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { JSX, Ref } from 'react'

/** A button to appear in the hamburger menu or to navigation bar. */
export function NavButton({
  icon,
  iconElement,
  text,
  disabled = false,
  ref,
  ...props
}: {
  icon?: IconDefinition
  iconElement?: JSX.Element
  text: string
  disabled?: boolean
  ref?: Ref<HTMLAnchorElement>
} & React.AnchorHTMLAttributes<HTMLAnchorElement>) {
  // note: it seems that we can just leave the `target="_blank"` and it has no
  // effect on links without a `href`. If not, add `if (href)` statement here...
  return (
    <a
      {...props}
      ref={ref}
      className={`nav-link${disabled ? ' disabled' : ''}${props.className ? ` ${props.className}` : ''}`}
      aria-disabled={disabled || undefined}
      onClick={disabled ? (e) => e.preventDefault() : props.onClick}
      target="_blank"
    >
      {iconElement ?? <FontAwesomeIcon icon={icon!} />}&nbsp;<span>{text}</span>
    </a>
  )
}
