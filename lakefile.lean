import Lake
open Lake DSL

package «representational-incompleteness» where
  leanOptions := #[⟨`autoImplicit, false⟩]

/-
  Mathlib is a **dependency** of this project. Do **not** compile all of Mathlib from
  source locally: after `lake update`, run **`lake exe cache get`** to download
  pre-built `.olean` bundles into `~/.cache/mathlib/`, then `lake build` only
  compiles this repo’s files. See `../docs/lean_mathlib_cache_workflow.md`.
-/

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.29.0-rc6"

@[default_target]
lean_lib RepresentationalIncompleteness where
  roots := #[`RepresentationalIncompleteness]
