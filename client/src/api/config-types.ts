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
}
