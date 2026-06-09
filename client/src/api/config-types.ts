import { JSX } from 'react'

export type LeanWebConfig = {
  /** Where the server is located. Use `null` to not display this information. */
  serverCountry: string | null
  /** Contact details of the server maintainer. Used in Privacy Policy and Impressum.
   * Use `null` to not display this information.
   * Note: This will be embedded inside a `<p>` tag! (example: `<>Hans Muster<br />hans@nowhere.com</>`)
   */
  contactDetails: JSX.Element | null
  /** Additional legal information shown in impressum alongside the contact details.
   * Use `null` to not display this information.
   * (example: `<><p>vat number: 000</p><>`)
   */
  impressum: JSX.Element | null
  /** Base href for a comparator live deployment that encourages the verification of proofs from untrusted sources.
   * If `null`, the "Can I Trust This Proof?" button will be hidden.
   * (example: `"https://comparator.live.lean-lang.org/"`)
   */
  comparator: string | null
  /** URLs to safelist so that refer links do not prompt a popup highlighting the "Can I Trust This Proof?" button.
   * Ignored if `comparator` option is `null`.
   */
  comparatorSafeList: (string | RegExp)[] | null
}
