# Adding Projects

To add a new project, one needs to add a lean project here.

Projects can be any Lean projects.

1. You can build the lean project manually. For automatic updates, your project should include a file `ProjectName/build.sh` which can be
  executed to build the project. See [lean4web-tools](https://github.com/hhu-adam/lean4web-tools) for an example.
2. Your project should add the dependency
    ```lean
    require webeditor from git
        "https://github.com/hhu-adam/lean4web-tools.git" @ "main"
    ```
    in its `lakefile.lean`. This package adds some simple tools like `#package_version`.
3. For a project to appear in the settings, you need to add it to `config.json`:
  add a new entry `{folder: "_", name: "_"}` to `projects`, where "folder" is the
  folder name inside `Projects/` and "name" is the free-text display name.

* Optionally, you can also specify examples in the `config.json` each of these
    examples will appear under "Examples" in the menu. A full project entry would then
    look as follows:
    ```
    { "folder": "folder name inside `Projects/`",
      "name": "My Custom Lean Demo",
      "examples": [
        { "file": "path/inside/the/lean/package.lean",
          "name": "My Cool Example"},
        ...
      ]
    }
    ```
* Compare to the entry for the `mathlib-demo` project.
