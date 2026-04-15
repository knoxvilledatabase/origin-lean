/-
Extracted from Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Restrict.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Restriction of the continuous functional calculus to a scalar subring

The main declaration in this file is:

+ `SpectrumRestricts.cfc`: builds a continuous functional calculus over a subring of scalars.
  This is used for automatically deriving the continuous functional calculi on selfadjoint or
  positive elements from the one for normal elements.

This will allow us to take an instance of the
`ContinuousFunctionalCalculus ℂ A IsStarNormal` and produce both of the instances
`ContinuousFunctionalCalculus ℝ A IsSelfAdjoint` and `ContinuousFunctionalCalculus ℝ≥0 A (0 ≤ ·)`
simply by proving:

1. `IsSelfAdjoint x ↔ IsStarNormal x ∧ SpectrumRestricts Complex.re x`,
2. `0 ≤ x ↔ IsSelfAdjoint x ∧ SpectrumRestricts Real.toNNReal x`.
-/

open Set Topology

namespace SpectrumRestricts

def homeomorph {R S A : Type*} [Semifield R] [Semifield S] [Ring A]
    [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] [TopologicalSpace R]
    [TopologicalSpace S] [ContinuousSMul R S] {a : A} {f : C(S, R)} (h : SpectrumRestricts a f) :
    spectrum S a ≃ₜ spectrum R a where
  toFun := MapsTo.restrict f _ _ h.subset_preimage
  invFun := MapsTo.restrict (algebraMap R S) _ _ (image_subset_iff.mp h.algebraMap_image.subset)
  left_inv x := Subtype.ext <| h.rightInvOn x.2
  right_inv x := Subtype.ext <| h.left_inv x

lemma compactSpace {R S A : Type*} [Semifield R] [Semifield S] [Ring A]
    [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] [TopologicalSpace R]
    [TopologicalSpace S] {a : A} (f : C(S, R)) (h : SpectrumRestricts a f)
    [h_cpct : CompactSpace (spectrum S a)] : CompactSpace (spectrum R a) := by
  rw [← isCompact_iff_compactSpace] at h_cpct ⊢
  exact h.image ▸ h_cpct.image (map_continuous f)

universe u v w
