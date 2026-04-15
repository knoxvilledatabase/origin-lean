/-
Extracted from LinearAlgebra/TensorAlgebra/Grading.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Results about the grading structure of the tensor algebra

The main result is `TensorAlgebra.gradedAlgebra`, which says that the tensor algebra is a
ℕ-graded algebra.
-/

namespace TensorAlgebra

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

open scoped DirectSum

variable (R M)

nonrec def GradedAlgebra.ι : M →ₗ[R] ⨁ i : ℕ, ↥(LinearMap.range (ι R : M →ₗ[_] _) ^ i) :=
  DirectSum.lof R ℕ (fun i => ↥(LinearMap.range (ι R : M →ₗ[_] _) ^ i)) 1 ∘ₗ
    (ι R).codRestrict _ fun m => by simpa only [pow_one] using LinearMap.mem_range_self _ m

variable {R M}

-- INSTANCE (free from Core): gradedAlgebra

end TensorAlgebra
