import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"@"v4.24.0"

package mathlibStable {
  -- add package configuration options here
}

@[default_target]
lean_lib MathlibStable {
  -- add library configuration options here
}
