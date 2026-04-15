/-
Extracted from RingTheory/Finiteness/Cofinite.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Co-finitely generated submodules

This files defines the notion of a co-finitely generated submodule. A submodule `S` of a module
`M` is co-finitely generated (or CoFG for short) if the quotient of `M` by `S` is finitely
generated (i.e. FG).

## Main declarations

- `Submodule.CoFG` expresses that a submodule is co-finitely generated.

-/

namespace Submodule

section Ring

variable {R : Type*} [Ring R]

variable {M : Type*} [AddCommGroup M] [Module R M]

abbrev CoFG (S : Submodule R M) : Prop := Module.Finite R (M ⧸ S)
