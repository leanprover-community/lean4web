/**
 * This file contains the documentation of the existing `config` options
*/

/** An example can be any Lean file which belongs to the project.
 * The editor just reads the file content, but it makes sense for maintainability
 * that you ensure the Lean project actually builds the file. */
interface Example {
  /** File to load; relative path in `lean4web/Projects/<projectfolder>/` */
  file: string,
  /** Display name used in the `Examples` menu */
  name: string
}

/** You can add any Lean Project under `lean4web/Projects/` and add it here to use it in the
 * web editor. Note that you will need to manually build your project. Alternatively
 * you can add a file `lean4web/Projects/myProject/build.sh` which contains the instructions
 * to update & build the project.
 */
interface Project {
  /** The folder containing the Lean project; the folder is expected to be in `lean4web/Projects/`.
   *  The folder name will appear in the URL.
   */
  folder: string,
  /** Display name; shown in selection menu */
  name: string,
  /** A list of examples which are added under the menu `Examples` */
  examples?: Example[]
}

export type { Example, Project }
