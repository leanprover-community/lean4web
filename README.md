[![GitHub license](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](https://github.com/leanprover-community/lean4web/blob/main/LICENSE)
[![(Runtime) Build and Test](https://github.com/leanprover-community/lean4web/actions/workflows/build.yml/badge.svg)](https://github.com/leanprover-community/lean4web/actions/workflows/build.yml)

# Lean 4 Web

This is a web version of Lean 4. There is a playground hosted at [live.lean-lang.org](https://live.lean-lang.org) and one at [lean.math.hhu.de](https://lean.math.hhu.de).

In contrast to the [Lean 3 web editor](https://github.com/leanprover-community/lean-web-editor), in this web editor, the Lean server is
running on a web server, and not in the browser.

## Scope of lean4web

- Provide a clean, minimalistic and easily accessible way to run some (smallish) Lean snippets
- Provide a simple way to run [MWEs](https://leanprover-community.github.io/mwe.html) from [Zulip](https://leanprover.zulipchat.com) with the latest [Mathlib](https://github.com/leanprover-community/mathlib4) installed.
- Provide a easy way to demonstrate some Lean code in talks/lecutres.
- Provide a easy way for newcomers to doodle with Lean before installing it.
- Provide a way to run some Lean code in a mobile context.

Currently, serious Lean code development and larger projects are considered out-of-scope. For these, it might be more suitable to look at a setup using Codespaces or Gitpot.

While `lean4web` looks very similar to VSCode with the [Lean4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4) installed - and it reuses much of that code - `lean4web` does not claim to be feature complete.

## Contribution

If you experience any problems, or have feature requests, please open an issue here!

PRs fixing issues are very welcome!

For new features, it's best to write an issue first to discuss them: For example, some functionality might be better implemented in [lean4monaco](https://github.com/hhu-adam/lean4monaco) which provides the key features and a discussion might be helpful to figure this out.

## Documentation

- [User Manual](./doc/Usage.md): Specification of `lean4web` features for the end user.
- [Installation](./doc/Installation.md): Instructions to install your own instance of `lean4web` on your own server
- [Development](./doc/Development.md): Instructions to contribute to `lean4web` itself
