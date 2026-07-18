import { faHandshake } from '@fortawesome/free-solid-svg-icons'
import ClickAwayListener from '@mui/material/ClickAwayListener'
import Popper from '@mui/material/Popper'
import { useAtom, useAtomValue } from 'jotai'
import { useState } from 'react'

import { lean4webConfig } from '../../config'
import { codeAtom } from '../editor/code-atoms'
import { localOnlySettingsAtom, settingsAtom } from '../settings/settings-atoms'
import { lightThemes } from '../settings/settings-types'
import { urlArgsStableAtom } from '../store/url-atoms'
import { parseArgs } from '../store/url-converters'
import { NavButton } from './NavButton'

interface ComparatorButtonProps {
  isInDropdown: boolean
}

const referrerNeedsComparator = (() => {
  // Never highlight comparator option if there's no code
  const args = parseArgs(window.location.hash)
  if (!args.code?.trim() && !args.codez?.trim()) return false // No warning for empty code or example-url-driven code

  // Highlight comparator if there's no referrer or if the referrer isn't safelisted
  if (!document.referrer) return true
  const referrer = new URL(document.referrer)
  if (!lean4webConfig.comparatorSafeList) return true
  return !lean4webConfig.comparatorSafeList.some((item) =>
    item instanceof RegExp ? referrer.hostname.match(item) : referrer.hostname === item,
  )
})()

export default function ComparatorButton({ isInDropdown }: ComparatorButtonProps) {
  const settings = useAtomValue(settingsAtom)
  const themeVariant = lightThemes.includes(settings.theme)
    ? 'light'
    : settings.theme === 'Cobalt'
      ? 'cobalt'
      : 'dark'
  const [comparatorWarningDismissed, setComparatorWarningDismissed] = useState(false)

  const urlArgs = useAtomValue(urlArgsStableAtom)
  const code = useAtomValue(codeAtom)
  const isUsingUrlCode = !!urlArgs?.url
  const [localOnlySettings, setLocalOnlySettings] = useAtom(localOnlySettingsAtom)

  const comparatorWarningEligible =
    !isInDropdown &&
    !isUsingUrlCode &&
    referrerNeedsComparator &&
    !localOnlySettings.ignoreComparatorWarning
  const [trustButtonEl, setTrustButtonEl] = useState<HTMLAnchorElement | null>(null)
  const [trustArrowEl, setTrustArrowEl] = useState<HTMLElement | null>(null)
  const comparatorWarningOpen =
    !!trustButtonEl && comparatorWarningEligible && !comparatorWarningDismissed

  return (
    <>
      {lean4webConfig.comparator && (
        <NavButton
          ref={isInDropdown ? undefined : setTrustButtonEl}
          icon={faHandshake}
          text={'Can I Trust This Proof?'}
          disabled={isUsingUrlCode}
          title={
            isUsingUrlCode
              ? 'Example urls not supported by Comparator tool! Edit the text to enable.'
              : (code ?? '').trim() === ''
                ? 'Open the Comparator verification tool'
                : 'Open this proof in the Comparator verification tool'
          }
          onClick={() => {
            window.location.assign(lean4webConfig.comparator + window.location.hash)
          }}
        />
      )}
      <Popper
        open={comparatorWarningOpen}
        anchorEl={trustButtonEl}
        placement="bottom-end"
        modifiers={[
          { name: 'flip', enabled: false },
          { name: 'offset', options: { offset: [0, 12] } },
          { name: 'arrow', enabled: true, options: { element: trustArrowEl, padding: 8 } },
        ]}
      >
        <ClickAwayListener onClickAway={() => setComparatorWarningDismissed(true)}>
          <div
            className={`comparator-warning ${themeVariant}`}
            role="status"
            aria-label="Verify untrusted proofs with Comparator"
          >
            <span className="comparator-warning-arrow" ref={setTrustArrowEl}></span>
            <button
              className="codicon codicon-close comparator-warning-close"
              aria-label="Dismiss"
              onClick={() => setComparatorWarningDismissed(true)}
            />
            <p>
              Don't trust proofs from untrusted sources unless they're validated against a trusted
              challenge. Use the <strong>Can I Trust This Proof?</strong> button to check this proof
              with the online version of Lean's Comparator tool.
            </p>
            <button
              className="comparator-warning-perma-dismiss"
              onClick={() => {
                setComparatorWarningDismissed(true)
                setLocalOnlySettings('ignoreComparatorWarning', true)
              }}
            >
              Don't show this again
            </button>
          </div>
        </ClickAwayListener>
      </Popper>{' '}
    </>
  )
}
