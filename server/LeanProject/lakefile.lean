import Lake
open Lake DSL

package leanProject {
  -- add package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"3fc135870439cc9dfad464e65684884eb751319e"

@[default_target]
lean_lib LeanProject {
  -- add library configuration options here
}
