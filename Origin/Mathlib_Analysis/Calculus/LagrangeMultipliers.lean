/-
Extracted from Analysis/Calculus/LagrangeMultipliers.lean
Genuine: 2 of 5 | Dissolved: 3 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.LinearAlgebra.Dual

/-!
# Lagrange multipliers

In this file we formalize the
[Lagrange multipliers](https://en.wikipedia.org/wiki/Lagrange_multiplier) method of solving
conditional extremum problems: if a function `φ` has a local extremum at `x₀` on the set
`f ⁻¹' {f x₀}`, `f x = (f₀ x, ..., fₙ₋₁ x)`, then the differentials of `fₖ` and `φ` are linearly
dependent. First we formulate a geometric version of this theorem which does not rely on the
target space being `ℝⁿ`, then restate it in terms of coordinates.

## TODO

Formalize Karush-Kuhn-Tucker theorem

## Tags

lagrange multiplier, local extremum

-/

open Filter Set

open scoped Topology Filter

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {f : E → F} {φ : E → ℝ} {x₀ : E}
  {f' : E →L[ℝ] F} {φ' : E →L[ℝ] ℝ}

theorem IsLocalExtrOn.range_ne_top_of_hasStrictFDerivAt
    (hextr : IsLocalExtrOn φ {x | f x = f x₀} x₀) (hf' : HasStrictFDerivAt f f' x₀)
    (hφ' : HasStrictFDerivAt φ φ' x₀) : LinearMap.range (f'.prod φ') ≠ ⊤ := by
  intro htop
  set fφ := fun x => (f x, φ x)
  have A : map φ (𝓝[f ⁻¹' {f x₀}] x₀) = 𝓝 (φ x₀) := by
    change map (Prod.snd ∘ fφ) (𝓝[fφ ⁻¹' {p | p.1 = f x₀}] x₀) = 𝓝 (φ x₀)
    rw [← map_map, nhdsWithin, map_inf_principal_preimage, (hf'.prod hφ').map_nhds_eq_of_surj htop]
    exact map_snd_nhdsWithin _
  exact hextr.not_nhds_le_map A.ge

-- DISSOLVED: IsLocalExtrOn.exists_linear_map_of_hasStrictFDerivAt

-- DISSOLVED: IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt_1d

-- DISSOLVED: IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt

theorem IsLocalExtrOn.linear_dependent_of_hasStrictFDerivAt {ι : Type*} [Finite ι] {f : ι → E → ℝ}
    {f' : ι → E →L[ℝ] ℝ} (hextr : IsLocalExtrOn φ {x | ∀ i, f i x = f i x₀} x₀)
    (hf' : ∀ i, HasStrictFDerivAt (f i) (f' i) x₀) (hφ' : HasStrictFDerivAt φ φ' x₀) :
    ¬LinearIndependent ℝ (Option.elim' φ' f' : Option ι → E →L[ℝ] ℝ) := by
  cases nonempty_fintype ι
  rw [Fintype.linearIndependent_iff]; push_neg
  rcases hextr.exists_multipliers_of_hasStrictFDerivAt hf' hφ' with ⟨Λ, Λ₀, hΛ, hΛf⟩
  refine ⟨Option.elim' Λ₀ Λ, ?_, ?_⟩
  · simpa [add_comm] using hΛf
  · simpa only [funext_iff, not_and_or, or_comm, Option.exists, Prod.mk_eq_zero, Ne,
      not_forall] using hΛ
