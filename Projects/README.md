# Adding Projects

To add a new project, one needs to add a lean project here.

Projects can be any Lean projects.

1. You can build the lean project manually. For automatic updates, your project should include a file `ProjectName/build.sh` which can be
  executed to build the project. See `lean4web-tools` for an example.
2. Your project should add the dependency
    ```lean
    require webeditor from git
        "https://github.com/hhu-adam/lean4web-tools.git" @ "main"
    ```
    in its `lakefile.lean`. This package adds some simple tools like `#package_version`.
4. For a project to appear in the settings, you need to modify `Settings.tsx` and add a new option with value `ProjectName`.
