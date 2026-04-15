/-
Extracted from Algebra/Lie/Graded.lean
Genuine: 2 of 4 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Graded Lie algebras

This file defines typeclasses `SetLike.GradedBracket` and `GradedLieAlgebra`, for working with Lie
algebras that are graded by a collection `ℒ` of submodules. The additivity of degree with respect to
the bracket product is encoded by an addition condition so we can avoid the usual difficulties of
adding elements of `A (i + j)` to elements of `A (j + i)`.

## Main definitions

* `SetLike.GradedBracket`: A typeclass for a bracket to respect an additive grading.
* `GradedLieAlgebra`: A typeclass for a Lie algebra to respect an additive grading.
* `LieDerivation.ofGradingSum`: A Lie derivation on the direct sum of graded pieces, that scalar-
  multiplies the pieces by an additive map applied to degree.
* `LieDerivation.ofGrading`: A Lie derivation on a graded Lie algebra, that scalar-multiplies graded
  pieces by an additive map applied to degree.

-/

open DirectSum

variable {ι σ R L : Type*}

section SetLike

class SetLike.GradedBracket [SetLike σ L] [Bracket L L] [Add ι] (ℒ : ι → σ) : Prop where
  /-- Bracket is homogeneous -/
  bracket_mem : ∀ ⦃i j k⦄ {gi gj}, i + j = k → gi ∈ ℒ i → gj ∈ ℒ j → ⁅gi, gj⁆ ∈ ℒ k

variable [DecidableEq ι] [AddCommMonoid ι] [CommRing R] [LieRing L] [LieAlgebra R L]
  (ℒ : ι → Submodule R L)

class GradedLieAlgebra extends SetLike.GradedBracket ℒ, DirectSum.Decomposition ℒ

end SetLike

namespace DirectSum

variable [DecidableEq ι] [AddCommMonoid ι] [CommRing R] [LieRing L] [LieAlgebra R L]
  (ℒ : ι → Submodule R L) [GradedLieAlgebra ℒ]

-- INSTANCE (free from Core): :

attribute [local simp] bracket_apply_apply
