import Lake
open Lake DSL

package webeditor {
  -- add package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"@"master"

@[default_target]
lean_lib Webeditor {
  -- add library configuration options here
}
