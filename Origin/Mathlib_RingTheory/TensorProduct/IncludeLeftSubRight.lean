/-
Extracted from RingTheory/TensorProduct/IncludeLeftSubRight.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Exactness properties of the difference map on tensor products

For an `R`-algebra `S`, we collect some properties of the `R`-linear map `S →ₗ[R] S ⊗[R] S` given
by `s ↦ s ⊗ₜ 1 - 1 ⊗ₜ s`.

## Main definitions

* `includeLeftSubRight`: The `R`-linear map sending `s : S` to `s ⊗ₜ 1 - 1 ⊗ₜ s`.
* `IsEffective`: Exactness of the sequence `R → S → S ⊗[R] S` where the first map is
  `Algebra.linearMap R S` and the second map is `includeLeftSubRight`. When `R` and `S` are
  commutative rings, this is equivalent to the inclusion `im (algebraMap : R → S) → S` being an
  effective monomorphism in `CommRingCat`.

## Main results

* `IsEffective.of_faithfullyFlat`: `IsEffective R S` is true for any faithfully flat `R`-algebra `S`

-/

open scoped TensorProduct

namespace Algebra

variable {R : Type*} [CommSemiring R]

variable {S : Type*} [Ring S] [Algebra R S]

namespace TensorProduct

section IncludeLeftSubRight

variable (R S) in

def includeLeftSubRight : S →ₗ[R] S ⊗[R] S :=
  includeLeft.toLinearMap - includeRight.toLinearMap
