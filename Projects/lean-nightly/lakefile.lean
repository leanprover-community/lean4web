import Lake
open Lake DSL

package leanlatest {
  -- add package configuration options here
  leanOptions := #[⟨`experimental.module, true⟩]
}

@[default_target]
lean_lib LeanNightly {
  -- add library configuration options here
}
