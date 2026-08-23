import { RefObject } from 'react'
import { NavButton } from './NavButton'

/**
 * The quicklink menu provides some "jump to" to jump
 * focus to important places.
 * This is to improve accessibility, see WCAG section 2.4
 */
export function QuickLinkMenu({
  ref,
  infoviewRef,
  editorRef,
}: {
  ref?: RefObject<HTMLButtonElement | null>
  infoviewRef: RefObject<HTMLButtonElement | null>
  editorRef: RefObject<HTMLButtonElement | null>
}) {
  return (
    <div className="quicklink">
      <span>Jump to:</span>
      <NavButton
        ref={ref}
        text="Infoview"
        aria-label="jump to Infoview"
        // TODO: focus infoview
      />
      <NavButton
        text="Editor"
        aria-label="jump to Editor"
        // TODO: focus editor
      />
    </div>
  )
}
