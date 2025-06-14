# Adding Projects

To add new projects, add any Lean project in the folder `Projects/`, e.g. `Projects/MyCoolProject/`.
You can either build your Lean project manually or you include a script
`Projects/MyCoolProject/build.sh` for automatic builds.
Usually a build script looks like this:

```
#!/usr/bin/env bash

# Operate in the directory where this file is located
cd $(dirname $0)

# add code here to update the project correctly

lake build
```

A project added this way can then be accessed online with `https://your.url.com/#project=MyCoolProject`.
For the project to appear in the Settings, you need to update `client/config/config.json` by adding
a new entry `{folder: "MyCoolProject", name: "My Cool Project"}` to `projects`; here `folder` is the
folder name inside `Projects/` and `name` is the free-text display name.

If you want to add Examples, you should add them as valid Lean files to your project and then expand
the config entry of your project in `config.json` as follows:

```
{ "folder": "MyCoolProject`",
  "name": "My Cool Project",
  "examples": [
    { "file": "MyCustomProject/Demo1.lean",
      "name": "My Cool Example" }
  ]
}
```

This will add an entry `My Cool Example` to the Example menu which loads
the file from `Projects/MyCoolProject/MyCoolProject/Demo1.lean`.

You might want to look at the provided `MathlibDemo` project for comparison.


**Important**: In order for lake to use any "leanOptions" specified in the projects lakefile, you must make sure there is a file `Projects/MyCoolProject/MyCoolProject.lean`
where folder name and file name coincide.