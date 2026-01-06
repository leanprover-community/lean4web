/**
 * This file contains the documentation of the existing `config` options
 */

import { JSX } from 'react'

/** An example can be any Lean file which belongs to the project.
 * The editor just reads the file content, but it makes sense for maintainability
 * that you ensure the Lean project actually builds the file. */
interface LeanWebExample {
  /** File to load; relative path in `lean4web/Projects/<projectfolder>/` */
  file: string
  /** Display name used in the `Examples` menu */
  name: string
}

/** You can add any Lean Project under `lean4web/Projects/` and add it here to use it in the
 * web editor. Note that you will need to manually build your project. Alternatively
 * you can add a file `lean4web/Projects/myProject/build.sh` which contains the instructions
 * to update & build the project.
 */
interface LeanWebProject {
  /** The folder containing the Lean project; the folder is expected to be in `lean4web/Projects/`.
   *  The folder name will appear in the URL.
   */
  folder: string
  /** Display name; shown in selection menu */
  name: string
  /** A list of examples which are added under the menu `Examples` */
  examples?: LeanWebExample[]
}

interface LeanWebConfig {
  projects: LeanWebProject[]
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

export type { LeanWebConfig, LeanWebExample, LeanWebProject }
