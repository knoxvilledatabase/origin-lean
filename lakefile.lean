import Lake
open Lake DSL

package «origin-lean» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.14.0"

@[default_target]
lean_lib Val where
  srcDir := "."

lean_lib Origin where
  srcDir := "."

lean_lib Proofs where
  srcDir := "."
