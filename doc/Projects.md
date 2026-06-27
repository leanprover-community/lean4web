- [Back to README](../README.md)
- [User Manual](./Usage.md)
- [Installation](./Installation.md)
- Adding Projects
- [Development](./Development.md)
- [Server Maintenance](./Maintenance.md)
- [Troubleshoot](./Troubleshoot.md)

# Adding Projects

It is possible to add additional projects to the web editor which can be selected from the
dropdown or through the URL.

The default directory for projects is `./Projects/` but this can be changed by setting
the environment variable `PROJECTS_BASE_PATH`. This needs to be set for the build process (`npm run build:server`) and for the production mode (`npm run prod` / `ecosystem.config.cjs`) and it contains a
relativ path from the project's root directory.

Inside this folder, new Lean projects can be created containing 2 special files:

- `leanweb-config.json` (mandatory)
- `leanweb-build.sh` (optional)

The name of the folder is simultaneously the key used in the URL, e.g. a project in the folder `MyCoolProject` can be accessed via `lean.your.website.com/#project=MyCoolProject`.

You might want to look at the provided `MathlibDemo` project for comparison.

## project structure

Any lake project can be used as a project. However, same features make some assumptions:

- In order for `lake` to use any `leanOptions` specified in the project's lakefile, you must make sure there is a file `Projects/MyCoolProject/MyCoolProject.lean` where folder name and file name coincide.
- The download button creates a ZIP where the editor content is placed in `MyCoolProject/MyCoolProject.lean` and the files `lean_toolchain`, `lake-manifest.json`, `lakefile.lean` (or `lakefile.toml`) are copied over. In particular, if the lakefile defines other targets, the downloaded lake project might not work as there might be missing these files.

## project config

The file `leanweb-config.json` takes the following form:

```json
{
  "name": "Display name",
  "default": false,
  "hidden": false,
  "sortOrder": 0,
  "examples": [
    { "file": "MathlibDemo/Bijection.lean", "name": "Example's display name" },
    ...
  ]
}
```

- `name`: The display name of the project as shown in the dropdown menu. The substrings `_Vers_` and
  `_LeanVers_` in the project name will be replaced by indicators of which version is being used:
  - If the toolchain is in a recognized format (a regular release like `v4.30.0-rc1` or nightly
    release like `2026-04-04`), then `_Vers_` will be replaced by the version number (e.g.
    `v4.30.0-rc1`) and `_LeanVers_` will be replaced by "Lean" followed by the version number (e.g.
    `Lean v4.30.0-rc1`)
  - If the toolchain is not in a recognized format, both `_Vers_` and `_LeanVers_` will be replaced
    by "Lean".
- `default`: There must be exactly one project with this set to `true`. This is the project loaded
  by default and when no project is specified in the url.
- `hidden`: If set to `true`, then the project does not appear in the dropdown and can
  only be accessed via direct link.
- `sortOrder`(non-negative number): sort order of the projects in the dropdown. The default always
  comes first, then projects with higher `sortOrder` value. Ties are resolved alphabetically.
- `examples`: list of examples. The path is relativ to the project's directory, e.g.
  `{PROJECTS_BASE_PATH}/{PROJECT_FOLDER}/{EXAMPLE_PATH.lean}`

## automatic builds

If the project contains a file `leanweb-build.sh`, it will be executed as part of `npm run build:server`.
This can be used to automatically update and build the project. A typical build script could look like
this:

```bash
#!/usr/bin/env bash

# Operate in the directory where this file is located
cd $(dirname $0)

# add code here to update the project correctly

lake build
```

If no build script exists, you must build your Lean projects manually.
