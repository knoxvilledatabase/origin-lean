/-
Extracted from Algebra/Algebra/Subalgebra/Pointwise.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Pointwise actions on subalgebras.

If `R'` acts on an `R`-algebra `A` (so that `R'` and `R` actions commute)
then we get an `R'` action on the collection of `R`-subalgebras.
-/

namespace Subalgebra

section Pointwise

variable {R : Type*} {A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

theorem mul_toSubmodule_le (S T : Subalgebra R A) :
    Subalgebra.toSubmodule S * Subalgebra.toSubmodule T ≤ Subalgebra.toSubmodule (S ⊔ T) := by
  rw [Submodule.mul_le]
  intro y hy z hz
  simp only [mem_toSubmodule]
  exact mul_mem (Algebra.mem_sup_left hy) (Algebra.mem_sup_right hz)
