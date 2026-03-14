import { atom } from 'jotai'
import { atomWithQuery } from 'jotai-tanstack-query'

import { LeanWebProject } from '../api/project-types'
import { urlArgsAtom, urlArgsStableAtom } from './url-atoms'

const projectsQueryAtom = atomWithQuery<LeanWebProject[]>((get) => ({
  queryKey: ['projects'],
  queryFn: async () => {
    const res = await fetch(`/api/projects`)
    return res.json()
  },
}))

/** Sort alphabetically while the `default` project always comes first */
function sortProjects(p: LeanWebProject, q: LeanWebProject): number {
  if (p.config.default) return -1
  if (q.config.default) return 1
  return p.config.name.localeCompare(q.config.name)
}

/** All available projects */
export const projectsAtom = atom((get) => {
  const query = get(projectsQueryAtom)
  return { ...query, data: query.data?.sort(sortProjects) ?? [] }
})

export const defaultProjectAtom = atom((get) => {
  const projects = get(projectsAtom).data
  if (projects.length === 0) return null
  const defaultProjects = projects.filter((it) => it.config.default)

  if (defaultProjects.length === 0) {
    console.warn(`Expected exactly one default project, but found none.`)
    return projects[0]
  }
  if (defaultProjects.length > 1) {
    console.error(`Expected exactly one default project, but found ${defaultProjects.length}`)
  }
  return defaultProjects[0]
})

/** The currently selected project */
export const currentProjectAtom = atom(
  (get) => {
    const urlArgProject = get(urlArgsStableAtom).project
    const defaultProject = get(defaultProjectAtom)
    const allProjects = get(projectsAtom).data
    if (!urlArgProject) return defaultProject
    if (!urlArgProject) return defaultProject
    return (
      allProjects.find((it) => it.folder.toLowerCase() == urlArgProject.toLowerCase()) ??
      defaultProject
    )
  },
  (get, set, project: string) => {
    const urlArgs = get(urlArgsStableAtom)
    const defaultProject = get(defaultProjectAtom)
    set(urlArgsAtom, {
      ...urlArgs,
      project:
        defaultProject == undefined || project !== defaultProject.folder ? project : undefined,
    })
  },
)

/** Visible projects */
export const visibleProjectsAtom = atom((get) => {
  const current = get(currentProjectAtom)
  const visible = get(projectsAtom).data.filter(
    (it) => !it.config.hidden || (current && it.folder == current.folder),
  )
  return visible
})
