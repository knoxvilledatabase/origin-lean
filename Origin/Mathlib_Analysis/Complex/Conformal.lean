/-
Extracted from Analysis/Complex/Conformal.lean
Genuine: 2 of 7 | Dissolved: 5 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Analysis.Calculus.Conformal.NormedSpace
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.Complex.FiniteDimensional

/-!
# Conformal maps between complex vector spaces

We prove the sufficient and necessary conditions for a real-linear map between complex vector spaces
to be conformal.

## Main results

* `isConformalMap_complex_linear`: a nonzero complex linear map into an arbitrary complex
                                   normed space is conformal.
* `isConformalMap_complex_linear_conj`: the composition of a nonzero complex linear map with
                                        `conj` is complex linear.
* `isConformalMap_iff_is_complex_or_conj_linear`: a real linear map between the complex
                                                  plane is conformal iff it's complex
                                                  linear or the composition of
                                                  some complex linear map and `conj`.

* `DifferentiableAt.conformalAt` states that a real-differentiable function with a nonvanishing
  differential from the complex plane into an arbitrary complex-normed space is conformal at a point
  if it's holomorphic at that point. This is a version of Cauchy-Riemann equations.

* `conformalAt_iff_differentiableAt_or_differentiableAt_comp_conj` proves that a real-differential
  function with a nonvanishing differential between the complex plane is conformal at a point if and
  only if it's holomorphic or antiholomorphic at that point.

## Warning

Antiholomorphic functions such as the complex conjugate are considered as conformal functions in
this file.

## TODO

* The classical form of Cauchy-Riemann equations
* On a connected open set `u`, a function which is `ConformalAt` each point is either holomorphic
throughout or antiholomorphic throughout.
-/

noncomputable section

open Complex ContinuousLinearMap ComplexConjugate

theorem isConformalMap_conj : IsConformalMap (conjLIE : ℂ →L[ℝ] ℂ) :=
  conjLIE.toLinearIsometry.isConformalMap

section ConformalIntoComplexNormed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]

-- DISSOLVED: isConformalMap_complex_linear

-- DISSOLVED: isConformalMap_complex_linear_conj

end ConformalIntoComplexNormed

section ConformalIntoComplexPlane

open ContinuousLinearMap

variable {g : ℂ →L[ℝ] ℂ}

theorem IsConformalMap.is_complex_or_conj_linear (h : IsConformalMap g) :
    (∃ map : ℂ →L[ℂ] ℂ, map.restrictScalars ℝ = g) ∨
      ∃ map : ℂ →L[ℂ] ℂ, map.restrictScalars ℝ = g ∘L ↑conjCLE := by
  rcases h with ⟨c, -, li, rfl⟩
  obtain ⟨li, rfl⟩ : ∃ li' : ℂ ≃ₗᵢ[ℝ] ℂ, li'.toLinearIsometry = li :=
    ⟨li.toLinearIsometryEquiv rfl, by ext1; rfl⟩
  rcases linear_isometry_complex li with ⟨a, rfl | rfl⟩
  -- let rot := c • (a : ℂ) • ContinuousLinearMap.id ℂ ℂ,
  · refine Or.inl ⟨c • (a : ℂ) • ContinuousLinearMap.id ℂ ℂ, ?_⟩
    ext1
    simp
  · refine Or.inr ⟨c • (a : ℂ) • ContinuousLinearMap.id ℂ ℂ, ?_⟩
    ext1
    simp

-- DISSOLVED: isConformalMap_iff_is_complex_or_conj_linear

end ConformalIntoComplexPlane

/-! ### Conformality of real-differentiable complex maps -/

section Conformality

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {z : ℂ} {f : ℂ → E}

-- DISSOLVED: DifferentiableAt.conformalAt

-- DISSOLVED: conformalAt_iff_differentiableAt_or_differentiableAt_comp_conj

end Conformality
