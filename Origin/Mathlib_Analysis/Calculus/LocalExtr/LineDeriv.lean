/-
Extracted from Analysis/Calculus/LocalExtr/LineDeriv.lean
Genuine: 11 of 20 | Dissolved: 0 | Infrastructure: 9
-/
import Origin.Core

/-!
# Local extremum and line derivatives

If `f` has a local extremum at a point, then the derivative at this point is zero.
In this file we prove several versions of this fact for line derivatives.
-/

open Function Set Filter

open scoped Topology

section Module

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {f : E → ℝ} {s : Set E} {a b : E} {f' : ℝ}

theorem IsExtrFilter.hasLineDerivAt_eq_zero {l : Filter E} (h : IsExtrFilter f l a)
    (hd : HasLineDerivAt ℝ f f' a b) (h' : Tendsto (fun t : ℝ ↦ a + t • b) (𝓝 0) l) : f' = 0 :=
  IsLocalExtr.hasDerivAt_eq_zero (IsExtrFilter.comp_tendsto (by simpa using h) h') hd

theorem IsExtrFilter.lineDeriv_eq_zero {l : Filter E} (h : IsExtrFilter f l a)
    (h' : Tendsto (fun t : ℝ ↦ a + t • b) (𝓝 0) l) : lineDeriv ℝ f a b = 0 := by
  classical
  exact if hd : LineDifferentiableAt ℝ f a b then
    h.hasLineDerivAt_eq_zero hd.hasLineDerivAt h'
  else
    lineDeriv_zero_of_not_lineDifferentiableAt hd

theorem IsExtrOn.hasLineDerivAt_eq_zero (h : IsExtrOn f s a) (hd : HasLineDerivAt ℝ f f' a b)
    (h' : ∀ᶠ t : ℝ in 𝓝 0, a + t • b ∈ s) : f' = 0 :=
  IsExtrFilter.hasLineDerivAt_eq_zero h hd <| tendsto_principal.2 h'

theorem IsExtrOn.lineDeriv_eq_zero (h : IsExtrOn f s a) (h' : ∀ᶠ t : ℝ in 𝓝 0, a + t • b ∈ s) :
    lineDeriv ℝ f a b = 0 :=
  IsExtrFilter.lineDeriv_eq_zero h <| tendsto_principal.2 h'

theorem IsExtrOn.lineDerivWithin_eq_zero (h : IsExtrOn f s a)
    (h' : ∀ᶠ t : ℝ in 𝓝 0, a + t • b ∈ s) : lineDerivWithin ℝ f s a b = 0 := by
  classical
  exact if hd : LineDifferentiableWithinAt ℝ f s a b then
    h.hasLineDerivWithinAt_eq_zero hd.hasLineDerivWithinAt h'
  else
    lineDerivWithin_zero_of_not_lineDifferentiableWithinAt hd

end Module

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]
  {f : E → ℝ} {s : Set E} {a b : E} {f' : ℝ}

theorem IsLocalExtr.hasLineDerivAt_eq_zero (h : IsLocalExtr f a) (hd : HasLineDerivAt ℝ f f' a b) :
    f' = 0 :=
  IsExtrFilter.hasLineDerivAt_eq_zero h hd <| Continuous.tendsto' (by fun_prop) _ _ (by simp)

theorem IsLocalExtr.lineDeriv_eq_zero (h : IsLocalExtr f a) : lineDeriv ℝ f a = 0 :=
  funext fun b ↦ IsExtrFilter.lineDeriv_eq_zero h <| Continuous.tendsto' (by fun_prop) _ _ (by simp)

theorem IsLocalMin.hasLineDerivAt_eq_zero (h : IsLocalMin f a) (hd : HasLineDerivAt ℝ f f' a b) :
    f' = 0 :=
  IsLocalExtr.hasLineDerivAt_eq_zero (.inl h) hd

theorem IsLocalMin.lineDeriv_eq_zero (h : IsLocalMin f a) : lineDeriv ℝ f a = 0 :=
  IsLocalExtr.lineDeriv_eq_zero (.inl h)

theorem IsLocalMax.hasLineDerivAt_eq_zero (h : IsLocalMax f a) (hd : HasLineDerivAt ℝ f f' a b) :
    f' = 0 :=
  IsLocalExtr.hasLineDerivAt_eq_zero (.inr h) hd

theorem IsLocalMax.lineDeriv_eq_zero (h : IsLocalMax f a) : lineDeriv ℝ f a = 0 :=
  IsLocalExtr.lineDeriv_eq_zero (.inr h)
