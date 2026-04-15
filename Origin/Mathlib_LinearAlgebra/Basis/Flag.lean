/-
Extracted from LinearAlgebra/Basis/Flag.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Flag of submodules defined by a basis

In this file we define `Basis.flag b k`, where `b : Basis (Fin n) R M`, `k : Fin (n + 1)`,
to be the subspace spanned by the first `k` vectors of the basis `b`.

We also prove some lemmas about this definition.
-/

open Set Submodule

namespace Module.Basis

section Semiring

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {n : ℕ} {b : Basis (Fin n) R M}
  {i j : Fin (n + 1)}

def flag (b : Basis (Fin n) R M) (k : Fin (n + 1)) : Submodule R M :=
  .span R <| b '' {i | i.castSucc < k}
