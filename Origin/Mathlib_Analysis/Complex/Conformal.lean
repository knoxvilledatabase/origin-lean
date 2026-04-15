/-
Extracted from Analysis/Complex/Conformal.lean
Genuine: 4 of 9 | Dissolved: 5 | Infrastructure: 0
-/
import Origin.Core

/-!
# Conformal maps between complex vector spaces

We prove the sufficient and necessary conditions for a real-linear map between complex vector spaces
to be conformal.

## Main results

* `isConformalMap_complex_linear`: a nonzero complex linear map into an arbitrary complex normed
  space is conformal.

* `isConformalMap_complex_linear_conj`: the composition of a nonzero complex linear map with `conj`
  is complex linear.

* `isConformalMap_iff_is_complex_or_conj_linear`: a real linear map between the complex plane is
  conformal iff it's complex linear or the composition of some complex linear map and `conj`.

* `DifferentiableAt.conformalAt` states that a real-differentiable function with a nonvanishing
  differential from the complex plane into an arbitrary complex-normed space is conformal at a point
  if it's holomorphic at that point. This is a version of Cauchy-Riemann equations.

* `conformalAt_iff_differentiableAt_or_differentiableAt_comp_conj` proves that a real-differential
  function with a nonvanishing differential between the complex plane is conformal at a point if and
  only if it's holomorphic or antiholomorphic at that point.

* `differentiableWithinAt_complex_iff_differentiableWithinAt_real` and
  `differentiableAt_complex_iff_differentiableAt_real` characterize complex differentiability in
  terms of the classic Cauchy-Riemann equation.

## Warning

Antiholomorphic functions such as the complex conjugate are considered as conformal functions in
this file.

## TODO

* On a connected open set `u`, a function which is `ConformalAt` each point is either holomorphic
  throughout or antiholomorphic throughout.
-/

noncomputable section

open Complex ContinuousLinearMap ComplexConjugate

theorem isConformalMap_conj : IsConformalMap (conjLIE : ℂ →L[ℝ] ℂ) :=
  conjLIE.toLinearIsometry.isConformalMap

section ConformalIntoComplexNormed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]

set_option backward.isDefEq.respectTransparency false in

-- DISSOLVED: isConformalMap_complex_linear

set_option backward.isDefEq.respectTransparency false in

-- DISSOLVED: isConformalMap_complex_linear_conj

end ConformalIntoComplexNormed

section ConformalIntoComplexPlane

open ContinuousLinearMap

variable {g : ℂ →L[ℝ] ℂ}

set_option backward.isDefEq.respectTransparency false in

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

set_option backward.isDefEq.respectTransparency false in

-- DISSOLVED: DifferentiableAt.conformalAt

set_option backward.isDefEq.respectTransparency false in

-- DISSOLVED: conformalAt_iff_differentiableAt_or_differentiableAt_comp_conj

end Conformality

/-!
### The Cauchy-Riemann Equation for Complex-Differentiable Functions
-/

section CauchyRiemann

open Complex

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : ℂ → E} {x : ℂ} {s : Set ℂ}

set_option backward.isDefEq.respectTransparency false in

lemma real_linearMap_map_smul_complex {ℓ : ℂ →ₗ[ℝ] E} (h : ℓ I = I • ℓ 1) (a b : ℂ) :
    ℓ (a • b) = a • ℓ b := by
  rw [← re_add_im a, ← re_add_im b, ← smul_eq_mul _ I, ← smul_eq_mul _ I]
  have t₀ : ((a.im : ℂ) • I) • (b.re : ℂ) = (↑(a.im * b.re) : ℂ) • I := by
    simp only [smul_eq_mul, ofReal_mul, ← mul_assoc, mul_comm _ I]
  have t₁ : ((a.im : ℂ) • I) • (b.im : ℂ) • I = (↑(- a.im * b.im) : ℂ) • (1 : ℂ) := by
    simp [mul_mul_mul_comm _ I]
  simp only [add_smul, smul_add, ℓ.map_add, t₀, t₁]
  repeat rw [Complex.coe_smul, ℓ.map_smul]
  have t₂ {r : ℝ} : ℓ (r : ℂ) = r • ℓ (1 : ℂ) := by simp [← ℓ.map_smul]
  simp only [t₂, h]
  match_scalars
  simp [mul_mul_mul_comm _ I]
  ring

def LinearMap.complexOfReal (ℓ : ℂ →ₗ[ℝ] E) (h : ℓ I = I • ℓ 1) : ℂ →ₗ[ℂ] E where
  __ := ℓ
  map_smul' := real_linearMap_map_smul_complex h
