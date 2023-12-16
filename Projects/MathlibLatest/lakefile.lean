import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"@"master"

require webeditor from ".." / "Webeditor"

package mathlibLatest {
  -- add package configuration options here
}

@[default_target]
lean_lib MathlibLatest {
  -- add library configuration options here
}
