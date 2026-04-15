/-
Extracted from Analysis/Seminorm.lean
Genuine: 4 of 6 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Seminorms

This file defines seminorms.

A seminorm is a function to the reals which is positive-semidefinite, absolutely homogeneous, and
subadditive. They are closely related to convex sets, and a topological vector space is locally
convex if and only if its topology is induced by a family of seminorms.

## Main declarations

For a module over a normed ring:
* `Seminorm`: A function to the reals that is positive-semidefinite, absolutely homogeneous, and
  subadditive.
* `normSeminorm 𝕜 E`: The norm on `E` as a seminorm.

## References

* [H. H. Schaefer, *Topological Vector Spaces*][schaefer1966]

## Tags

seminorm, locally convex, LCTVS
-/

assert_not_exists balancedCore

open NormedField Set Filter

open scoped NNReal Pointwise Topology Uniformity

variable {R R' 𝕜 𝕜₂ 𝕜₃ 𝕝 E E₂ E₃ F ι : Type*}

structure Seminorm (𝕜 : Type*) (E : Type*) [SeminormedRing 𝕜] [AddGroup E] [SMul 𝕜 E] extends
  AddGroupSeminorm E where
  /-- The seminorm of a scalar multiplication is the product of the absolute value of the scalar
  and the original seminorm. -/
  smul' : ∀ (a : 𝕜) (x : E), toFun (a • x) = ‖a‖ * toFun x

attribute [nolint docBlame] Seminorm.toAddGroupSeminorm

class SeminormClass (F : Type*) (𝕜 E : outParam Type*) [SeminormedRing 𝕜] [AddGroup E]
  [SMul 𝕜 E] [FunLike F E ℝ] : Prop extends AddGroupSeminormClass F E ℝ where
  /-- The seminorm of a scalar multiplication is the product of the absolute value of the scalar
  and the original seminorm. -/
  map_smul_eq_mul (f : F) (a : 𝕜) (x : E) : f (a • x) = ‖a‖ * f x

export SeminormClass (map_smul_eq_mul)

section Of

def Seminorm.of [SeminormedRing 𝕜] [AddCommGroup E] [Module 𝕜 E] (f : E → ℝ)
    (add_le : ∀ x y : E, f (x + y) ≤ f x + f y) (smul : ∀ (a : 𝕜) (x : E), f (a • x) = ‖a‖ * f x) :
    Seminorm 𝕜 E where
  toFun := f
  map_zero' := by rw [← zero_smul 𝕜 (0 : E), smul, norm_zero, zero_mul]
  add_le' := add_le
  smul' := smul
  neg' x := by rw [← neg_one_smul 𝕜, smul, norm_neg, ← smul, one_smul]

def Seminorm.ofSMulLE [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] (f : E → ℝ) (map_zero : f 0 = 0)
    (add_le : ∀ x y, f (x + y) ≤ f x + f y) (smul_le : ∀ (r : 𝕜) (x), f (r • x) ≤ ‖r‖ * f x) :
    Seminorm 𝕜 E :=
  Seminorm.of f add_le fun r x => by
    refine le_antisymm (smul_le r x) ?_
    by_cases h : r = 0
    · simp [h, map_zero]
    rw [← mul_le_mul_iff_right₀ (inv_pos.mpr (norm_pos_iff.mpr h))]
    rw [inv_mul_cancel_left₀ (norm_ne_zero_iff.mpr h)]
    specialize smul_le r⁻¹ (r • x)
    rw [norm_inv] at smul_le
    convert smul_le
    simp [h]

end Of

namespace Seminorm

section SeminormedRing

variable [SeminormedRing 𝕜]

section AddGroup

variable [AddGroup E]

section SMul

variable [SMul 𝕜 E]

-- INSTANCE (free from Core): instFunLike

-- INSTANCE (free from Core): instSeminormClass
