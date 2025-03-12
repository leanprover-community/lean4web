[![GitHub license](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](https://github.com/leanprover-community/lean4web/blob/main/LICENSE)
[![(Runtime) Build and Test](https://github.com/leanprover-community/lean4web/actions/workflows/build.yml/badge.svg)](https://github.com/leanprover-community/lean4web/actions/workflows/build.yml)


# Lean 4 Web

This is a web version of Lean 4. There is a playground hosted at [live.lean-lang.org](https://live.lean-lang.org) and one at [lean.math.hhu.de](https://lean.math.hhu.de).

In contrast to the [Lean 3 web editor](https://github.com/leanprover-community/lean-web-editor), in this web editor, the Lean server is
running on a web server, and not in the browser.

## Scope of lean4web

The main scope of `lean4web` is to provide an easy way to run [MWEs](https://leanprover-community.github.io/mwe.html) from [Zulip](https://leanprover.zulipchat.com) with the latest [Mathlib](https://github.com/leanprover-community/mathlib4) installed.

While `lean4web` looks very similar to VSCode with the [Lean4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4) installed - and it reuses much of that code - there is currently no official support by the [Lean FRO](https://lean-fro.org) and therefore `lean4web` does not claim to be feature complete. 

## Contribution

If you experience any problems, or have feature requests, please open an issue here!

PRs fixing issues are very welcome!

For new features, it's best to write an issue first to discuss them: For example, some functionality might be better implemented in [lean4monaco](https://github.com/hhu-adam/lean4monaco) which provides the key features and a discussion might be helpful to figure this out. 

## Documentation

- [User Manual](./doc/Usage.md): Specification of `lean4web` features for the end user.
- [Installation](./doc/Installation.md): Instructions to install your own instance of `lean4web` on your own server
- [Development](./doc/Development.md): Instructions to contribute to `lean4web` itself
