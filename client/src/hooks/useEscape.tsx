import { RefObject, useEffect } from 'react'

/** Hook which activates on `Esc` if the focus is within the component */
export function useEscape(
  ref: RefObject<HTMLElement | null>,
  onEscape: () => void,
) {
  useEffect(() => {
    const handler = (ev: KeyboardEvent) => {
      if (
        ev.key === 'Escape' &&
        ref.current?.contains(document.activeElement)
      ) {
        ev.stopPropagation()
        onEscape()
      }
    }

    document.addEventListener('keydown', handler)
    return () => document.removeEventListener('keydown', handler)
  }, [ref, onEscape])
}
