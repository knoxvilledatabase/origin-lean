/-
Extracted from LinearAlgebra/SesquilinearForm/Basic.lean
Genuine: 12 of 16 | Dissolved: 2 | Infrastructure: 2
-/
import Origin.Core

/-!
# Sesquilinear maps

This file provides properties about sesquilinear maps and forms. The maps considered are of the
form `M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] M`, where `I₁ : R₁ →+* R` and `I₂ : R₂ →+* R` are ring homomorphisms and
`M₁` is a module over `R₁`, `M₂` is a module over `R₂` and `M` is a module over `R`.
Sesquilinear forms are the special case that `M₁ = M₂`, `M = R₁ = R₂ = R`, and `I₁ = RingHom.id R`.
Taking additionally `I₂ = RingHom.id R`, then one obtains bilinear forms.

Sesquilinear maps are a special case of the bilinear maps defined in `BilinearMap.lean`, and many
basic lemmas about construction and elementary calculations are found there.

## Main declarations

* `IsOrtho`: states that two vectors are orthogonal with respect to a sesquilinear map
* `IsSymm`, `IsAlt`: states that a sesquilinear form is symmetric and alternating, respectively
* `orthogonalBilin` provides the orthogonal complement with respect to a sesquilinear form

## References

* <https://en.wikipedia.org/wiki/Sesquilinear_form#Over_arbitrary_rings>

## Tags

Sesquilinear form, Sesquilinear map
-/

open Module

variable {R R₁ R₂ R₃ M M₁ M₂ M₃ Mₗ₁ Mₗ₁' Mₗ₂ Mₗ₂' K K₁ K₂ V V₁ V₂ n : Type*}

namespace LinearMap

/-! ### Orthogonal vectors -/

section CommRing

variable [CommSemiring R] [CommSemiring R₁] [AddCommMonoid M₁] [Module R₁ M₁] [CommSemiring R₂]
  [AddCommMonoid M₂] [Module R₂ M₂] [AddCommMonoid M] [Module R M]
  {I₁ : R₁ →+* R} {I₂ : R₂ →+* R} {I₁' : R₁ →+* R}

def IsOrtho (B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] M) (x : M₁) (y : M₂) : Prop :=
  B x y = 0

theorem isOrtho_zero_left (B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] M) (x) : IsOrtho B (0 : M₁) x := by
  dsimp only [IsOrtho]
  rw [map_zero B, zero_apply]

theorem isOrtho_zero_right (B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] M) (x) : IsOrtho B x (0 : M₂) :=
  map_zero (B x)

theorem isOrtho_flip {B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₁'] M} {x y} : B.IsOrtho x y ↔ B.flip.IsOrtho y x := by
  simp_rw [isOrtho_def, flip_apply]

open scoped Function in -- required for scoped `on` notation

def IsOrthoᵢ (B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₁'] M) (v : n → M₁) : Prop :=
  Pairwise (B.IsOrtho on v)

theorem isOrthoᵢ_flip (B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₁'] M) {v : n → M₁} :
    B.IsOrthoᵢ v ↔ B.flip.IsOrthoᵢ v := by
  simp_rw [isOrthoᵢ_def]
  constructor <;> exact fun h i j hij ↦ h j i hij.symm

end CommRing

section Field

variable [Field K] [AddCommGroup V] [Module K V] [Field K₁] [AddCommGroup V₁] [Module K₁ V₁]
  [Field K₂] [AddCommGroup V₂] [Module K₂ V₂]
  {I₁ : K₁ →+* K} {I₂ : K₂ →+* K} {I₁' : K₁ →+* K} {J₁ : K →+* K} {J₂ : K →+* K}

-- DISSOLVED: ortho_smul_left

-- DISSOLVED: ortho_smul_right

theorem linearIndependent_of_isOrthoᵢ {B : V₁ →ₛₗ[I₁] V₁ →ₛₗ[I₁'] V} {v : n → V₁}
    (hv₁ : B.IsOrthoᵢ v) (hv₂ : ∀ i, ¬B.IsOrtho (v i) (v i)) : LinearIndependent K₁ v := by
  classical
    rw [linearIndependent_iff']
    intro s w hs i hi
    have : B (s.sum fun i : n ↦ w i • v i) (v i) = 0 := by rw [hs, map_zero, zero_apply]
    have hsum : (s.sum fun j : n ↦ I₁ (w j) • B (v j) (v i)) = I₁ (w i) • B (v i) (v i) := by
      apply Finset.sum_eq_single_of_mem i hi
      intro j _hj hij
      rw [isOrthoᵢ_def.1 hv₁ _ _ hij, smul_zero]
    simp_rw [B.map_sum₂, map_smulₛₗ₂, hsum] at this
    apply (map_eq_zero I₁).mp
    exact (smul_eq_zero.mp this).elim _root_.id (hv₂ i · |>.elim)

end Field

/-! ### Reflexive bilinear maps -/

section Reflexive

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [CommSemiring R₁] [AddCommMonoid M₁]
  [Module R₁ M₁] {I₁ : R₁ →+* R} {I₂ : R₁ →+* R} {B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₂] M}

def IsRefl (B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₂] M) : Prop :=
  ∀ x y, B x y = 0 → B y x = 0

namespace IsRefl

variable (H : B.IsRefl)

include H

theorem eq_zero : ∀ {x y}, B x y = 0 → B y x = 0 := fun {x y} ↦ H x y

theorem eq_iff {x y} : B x y = 0 ↔ B y x = 0 := ⟨H x y, H y x⟩

theorem ortho_comm {x y} : IsOrtho B x y ↔ IsOrtho B y x :=
  ⟨eq_zero H, eq_zero H⟩

theorem domRestrict (p : Submodule R₁ M₁) : (B.domRestrict₁₂ p p).IsRefl :=
  fun _ _ ↦ by
  simp_rw [domRestrict₁₂_apply]
  exact H _ _

end
