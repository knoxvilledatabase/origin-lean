/-
Extracted from LinearAlgebra/SesquilinearForm/Star.lean
Genuine: 4 of 5 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Sesquilinear forms over a star ring

This file provides some properties about sesquilinear forms `M →ₗ⋆[R] M →ₗ[R] R` when `R` is a
`StarRing`.
-/

open Module LinearMap

variable {R M n : Type*} [CommSemiring R] [StarRing R] [AddCommMonoid M] [Module R M]
  [Fintype n] [DecidableEq n]
  {B : M →ₗ⋆[R] M →ₗ[R] R} (b : Basis n R M)

lemma LinearMap.isSymm_iff_isHermitian_toMatrix : B.IsSymm ↔ (toMatrix₂ b b B).IsHermitian := by
  rw [isSymm_iff_basis b, Matrix.IsHermitian.ext_iff, forall_comm]
  simp [Eq.comm]

lemma star_dotProduct_toMatrix₂_mulVec (x y : n → R) :
    star x ⬝ᵥ (toMatrix₂ b b B).mulVec y = B (b.equivFun.symm x) (b.equivFun.symm y) :=
  dotProduct_toMatrix₂_mulVec b b B x y

lemma apply_eq_star_dotProduct_toMatrix₂_mulVec (x y : M) :
    B x y = star (b.repr x) ⬝ᵥ (toMatrix₂ b b B).mulVec (b.repr y) :=
  apply_eq_dotProduct_toMatrix₂_mulVec b b B x y

variable {R : Type*} [CommRing R] [StarRing R] [PartialOrder R] [Module R M]
  {B : M →ₗ⋆[R] M →ₗ[R] R} (b : Basis n R M)

lemma LinearMap.isPosSemidef_iff_posSemidef_toMatrix :
    B.IsPosSemidef ↔ (toMatrix₂ b b B).PosSemidef := by
  rw [isPosSemidef_def, Matrix.posSemidef_iff_dotProduct_mulVec]
  apply and_congr (B.isSymm_iff_isHermitian_toMatrix b)
  rw [isNonneg_def]
  refine ⟨fun h x ↦ ?_, fun h x ↦ ?_⟩
  · rw [star_dotProduct_toMatrix₂_mulVec]
    exact h _
  · rw [apply_eq_star_dotProduct_toMatrix₂_mulVec b]
    exact h _
