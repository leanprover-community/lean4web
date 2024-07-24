import Lake
open Lake DSL

package leanProject {
  -- add package configuration options here
}

lean_lib LeanProject {
  -- add library configuration options here
}

@[default_target]
lean_exe leanProject {
  root := `Main
}
