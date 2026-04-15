import Lake
open Lake DSL

package «origin-lean» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib Val where
  srcDir := "."

lean_lib Origin where
  srcDir := "."
