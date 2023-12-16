# Adding Projects

To add a new project, one needs to add a leanproject here.

It's important that the project has a file `ProjectName/ProjectName.lean` which imports
anything required! Moreover, there should be a file `ProjectName/build.sh` which
can be called to update the project.

A project would ideally import `import Webeditor from ".." / "Webeditor"` to allow
the custom lean tools to be available, but that's optional.

You might want to update `Settings.tsx` and add an option to switch to the added
project.
