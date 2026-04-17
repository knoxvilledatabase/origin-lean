import Lake
open Lake DSL

package «origin-lean» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

lean_lib «origin» where
  srcDir := "."
