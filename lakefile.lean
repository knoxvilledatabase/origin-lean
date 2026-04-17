import Lake
open Lake DSL

package «origin-lean» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

lean_lib «origin» where
  srcDir := "."

lean_lib «core» where
  srcDir := "."

lean_lib «laws» where
  srcDir := "."
