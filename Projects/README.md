# Adding Projects

To add new projects, add any Lean project in the folder `Projects/`, e.g. `Projects/my-cool-project/`.
You can either build your Lean project manually or you include a script
`Projects/my-cool-project/build.sh` for automatic builds.
Usually a build script looks like this:

```
#!/usr/bin/env bash

# Operate in the directory where this file is located
cd $(dirname $0)

# add code here to update the project correctly

lake build
```

A project added this way can then be accessed online with `https://your.url.com/#project=my-cool-project`.
For the project to appear in the Settings, you need to update `client/config/config.json` by adding
a new entry `{folder: "my-cool-project", name: "My Cool Project"}` to `projects`; here `folder` is the
folder name inside `Projects/` and `name` is the free-text display name.

If you want to add Examples, you should add them as valid Lean files to your project and then expand
the config entry of your project in `config.json` as follows:

```
{ "folder": "my-cool-project`",
  "name": "My Cool Project",
  "examples": [
    { "file": "MyCustomProject/Demo1.lean",
      "name": "My Cool Example" }
  ]
}
```

This will add an entry `My Cool Example` to the Example menu which loads
the file from `Projects/my-cool-project/MyCustomProject/Demo1.lean`.

You might want to look at the provided `MathlibDemo` project for comparison.
