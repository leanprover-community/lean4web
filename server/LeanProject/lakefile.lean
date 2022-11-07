import Lake
open Lake DSL

package leanProject {
  -- add package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"b902a2ae691979df0b5e19cc4200e817c6fdc463"

@[default_target]
lean_lib LeanProject {
  -- add library configuration options here
}
