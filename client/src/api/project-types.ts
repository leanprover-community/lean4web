/** An example can be any Lean file which belongs to the project.
 * The editor just reads the file content, but it makes sense for maintainability
 * that you ensure the Lean project actually builds the file. */
export type LeanWebExample = {
  /** File to load; relative path in `lean4web/Projects/<project_folder>/` */
  file: string
  /** Display name used in the `Examples` menu */
  name: string
}

/** Configuration from a project's `leanweb-config.json` file. */
export type LeanWebProjectConfig = {
  /** Display name; shown in selection menu */
  name: string
  /** Hidden projects do not appear in the dropdown and are only accessible through the direct link */
  hidden: boolean
  /** The default project. There must be exactly one project marked as default */
  default: boolean
  /** A list of examples which are added under the menu `Examples` */
  examples: LeanWebExample[]
}

/* A project */
export type LeanWebProject = {
  /* The folder name of the project. */
  folder: string
  config: LeanWebProjectConfig
}
