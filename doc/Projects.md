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

**Important**: In order for `lake` to use any `leanOptions` specified in the project's lakefile, you must make sure there is a file `Projects/MyCoolProject/MyCoolProject.lean`
where folder name and file name coincide.

## project config

The file `leanweb-config.json` takes the following form:

```json
{
  "name": "Display name",
  "default": false,
  "hidden": false,
  "examples": [
    { "file": "MathlibDemo/Bijection.lean", "name": "Example's display name" },
    ...
  ]
}
```

- `name`: The display name of the project as shown in the dropdown menu
- `default`: There must be exactly one project with this set to `true`. This is the project loaded
  by default and when no project is specified in the url.
- `hidden`: If set to `true`, then the project does not appear in the dropdown and can
  only be accessed via direct link.
- `examples`: list of examples. The path is relativ to the project's directory, e.g. `{PROJECTS_BASE_PATH}/{PROJECT_FOLDER}/{EXAMPLE_PATH.lean}`

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
