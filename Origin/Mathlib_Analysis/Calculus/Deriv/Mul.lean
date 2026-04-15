/-
Extracted from Analysis/Calculus/Deriv/Mul.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Derivative of `f x * g x`

In this file we prove formulas for `(f x * g x)'` and `(f x • g x)'`.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`Mathlib/Analysis/Calculus/Deriv/Basic.lean`.

## Keywords

derivative, multiplication
-/

universe u v w

noncomputable section

open scoped Topology Filter ENNReal

open Filter Asymptotics Set

open ContinuousLinearMap (smulRight smulRight_one_eq_iff)

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]

variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

variable {f : 𝕜 → F}

variable {f' : F}

variable {x : 𝕜}

variable {s : Set 𝕜}

variable {L : Filter (𝕜 × 𝕜)}

/-! ### Derivative of bilinear maps -/

namespace ContinuousLinearMap

variable {B : E →L[𝕜] F →L[𝕜] G} {u : 𝕜 → E} {v : 𝕜 → F} {u' : E} {v' : F}

theorem hasDerivWithinAt_of_bilinear
    (hu : HasDerivWithinAt u u' s x) (hv : HasDerivWithinAt v v' s x) :
    HasDerivWithinAt (fun x ↦ B (u x) (v x)) (B (u x) v' + B u' (v x)) s x := by
  simpa using (B.hasFDerivWithinAt_of_bilinear
    hu.hasFDerivWithinAt hv.hasFDerivWithinAt).hasDerivWithinAt

theorem hasDerivAt_of_bilinear (hu : x ∈ tsupport v → HasDerivAt u u' x)
    (hv : x ∈ tsupport u → HasDerivAt v v' x) :
    HasDerivAt (fun x ↦ B (u x) (v x)) (B (u x) v' + B u' (v x)) x := by
  by_cases hxu : x ∈ tsupport u
  · by_cases hxv : x ∈ tsupport v
    · simpa using (B.hasFDerivAt_of_bilinear (hu hxv).hasFDerivAt (hv hxu).hasFDerivAt).hasDerivAt
    · have hx : x ∉ tsupport fun x ↦ B (u x) (v x) :=
        mt (closure_mono (fun x ↦ mt fun h ↦ by simp [h]) ·) hxv
      convert HasDerivAt.of_notMem_tsupport hx
      simp [(hv hxu).unique <| .of_notMem_tsupport hxv, image_eq_zero_of_notMem_tsupport hxv]
  · have hx : x ∉ tsupport fun x ↦ B (u x) (v x) :=
      mt (closure_mono (fun x ↦ mt fun h ↦ by simp [h]) ·) hxu
    convert HasDerivAt.of_notMem_tsupport hx
    by_cases hxv : x ∈ tsupport v
    · simp [image_eq_zero_of_notMem_tsupport hxu, (hu hxv).unique <| .of_notMem_tsupport hxu]
    · simp [image_eq_zero_of_notMem_tsupport hxu, image_eq_zero_of_notMem_tsupport hxv]

theorem hasStrictDerivAt_of_bilinear (hu : HasStrictDerivAt u u' x) (hv : HasStrictDerivAt v v' x) :
    HasStrictDerivAt (fun x ↦ B (u x) (v x)) (B (u x) v' + B u' (v x)) x := by
  simpa using
    (B.hasStrictFDerivAt_of_bilinear hu.hasStrictFDerivAt hv.hasStrictFDerivAt).hasStrictDerivAt

theorem derivWithin_of_bilinear
    (hu : DifferentiableWithinAt 𝕜 u s x) (hv : DifferentiableWithinAt 𝕜 v s x) :
    derivWithin (fun y => B (u y) (v y)) s x =
      B (u x) (derivWithin v s x) + B (derivWithin u s x) (v x) := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (B.hasDerivWithinAt_of_bilinear hu.hasDerivWithinAt hv.hasDerivWithinAt).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

theorem deriv_of_bilinear (hu : x ∈ tsupport v → DifferentiableAt 𝕜 u x)
    (hv : x ∈ tsupport u → DifferentiableAt 𝕜 v x) :
    deriv (fun y => B (u y) (v y)) x = B (u x) (deriv v x) + B (deriv u x) (v x) :=
  (B.hasDerivAt_of_bilinear (fun hx ↦ (hu hx).hasDerivAt) fun hx ↦ (hv hx).hasDerivAt).deriv

end ContinuousLinearMap

section SMul

/-! ### Derivative of the multiplication of a scalar function and a vector function -/

variable {𝕜' : Type*} [NormedRing 𝕜'] [NormedAlgebra 𝕜 𝕜'] [Module 𝕜' F] [IsBoundedSMul 𝕜' F]
  [IsScalarTower 𝕜 𝕜' F] {c : 𝕜 → 𝕜'} {c' : 𝕜'}
