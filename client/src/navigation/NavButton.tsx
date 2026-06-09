import { IconDefinition } from '@fortawesome/free-solid-svg-icons'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { JSX, MouseEventHandler, Ref } from 'react'

/** A button to appear in the hamburger menu or to navigation bar. */
export function NavButton({
  icon,
  iconElement,
  text,
  title,
  onClick = () => {},
  href = undefined,
  disabled = false,
  ref,
}: {
  icon?: IconDefinition
  iconElement?: JSX.Element
  text: string
  title?: string
  onClick?: MouseEventHandler<HTMLAnchorElement>
  href?: string
  disabled?: boolean
  ref?: Ref<HTMLAnchorElement>
}) {
  // note: it seems that we can just leave the `target="_blank"` and it has no
  // effect on links without a `href`. If not, add `if (href)` statement here...
  return (
    <a
      ref={ref}
      className={`nav-link${disabled ? ' disabled' : ''}`}
      title={title}
      aria-disabled={disabled || undefined}
      onClick={disabled ? (e) => e.preventDefault() : onClick}
      href={href!}
      target="_blank"
    >
      {' '}
      {iconElement ?? <FontAwesomeIcon icon={icon!} />}&nbsp;{text}
    </a>
  )
}
