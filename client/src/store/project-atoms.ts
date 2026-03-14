import { atom } from 'jotai'
import { atomWithQuery } from 'jotai-tanstack-query'

import { urlArgsAtom, urlArgsStableAtom } from './url-atoms'

/* An example a project provides */
export interface Example {
  file: string
  name: string
}

/* A project's user configuration */
export type ProjectConfig = {
  name: string
  hidden: boolean
  default: boolean
  examples: Example[]
}

/* A project */
export type Project = {
  folder: string
  config: ProjectConfig
}

const projectsQueryAtom = atomWithQuery<Project[]>((get) => ({
  queryKey: ['projects'],
  queryFn: async () => {
    const res = await fetch(`/api/projects`)
    return res.json()
  },
}))

/** Sort alphabetically while the `default` project always comes first */
function sortProjects(p: Project, q: Project): number {
  if (p.config.default) return -1
  if (q.config.default) return 1
  return p.config.name.localeCompare(q.config.name)
}

/** All available projects */
export const projectsAtom = atom((get) => {
  const query = get(projectsQueryAtom)
  return { ...query, data: query.data?.sort(sortProjects) ?? [] }
})

export const defaultProjectFolderAtom = atom((get) => {
  const projects = get(projectsAtom).data
  if (projects.length === 0) return 'MathlibDemo' // TODO: is this correct?
  const defaultProjects = projects.filter((it) => it.config.default)

  if (defaultProjects.length === 0) {
    console.warn(`Expected exactly one default project, but found none.`)
    return projects[0].folder
  }
  if (defaultProjects.length > 1) {
    console.error(`Expected exactly one default project, but found ${defaultProjects.length}`)
  }
  return defaultProjects[0].folder
})

/** The currently selected project */
export const projectAtom = atom(
  (get) => {
    const urlArgs = get(urlArgsStableAtom)
    return urlArgs.project ?? get(defaultProjectFolderAtom)
  },
  (get, set, project: string) => {
    const urlArgs = get(urlArgsStableAtom)
    set(urlArgsAtom, {
      ...urlArgs,
      project: project !== get(defaultProjectFolderAtom) ? project : undefined,
    })
  },
)
