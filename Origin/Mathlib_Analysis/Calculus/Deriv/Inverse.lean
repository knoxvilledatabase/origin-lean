/-
Extracted from Analysis/Calculus/Deriv/Inverse.lean
Genuine: 6 of 18 | Dissolved: 12 | Infrastructure: 0
-/
import Origin.Core

/-!
# Inverse function theorem - the easy half

In this file we prove that `g' (f x) = (f' x)⁻¹` provided that `f` is strictly differentiable at
`x`, `f' x ≠ 0`, and `g` is a local left inverse of `f` that is continuous at `f x`. This is the
easy half of the inverse function theorem: the harder half states that `g` exists.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`Analysis/Calculus/Deriv/Basic`.

## Keywords

derivative, inverse function
-/

universe u v

open scoped Topology

open Filter Set

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]

variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable {f : 𝕜 → F}

variable {f' : F}

variable {s : Set 𝕜} {x : 𝕜} {c : F}

-- DISSOLVED: HasStrictDerivAt.hasStrictFDerivAt_equiv

-- DISSOLVED: HasDerivAt.hasFDerivAt_equiv

-- DISSOLVED: HasStrictDerivAt.of_local_left_inverse

-- DISSOLVED: OpenPartialHomeomorph.hasStrictDerivAt_symm

-- DISSOLVED: HasDerivAt.of_local_left_inverse

-- DISSOLVED: OpenPartialHomeomorph.hasDerivAt_symm

-- DISSOLVED: HasDerivWithinAt.tendsto_nhdsWithin_nhdsNE

-- DISSOLVED: HasDerivWithinAt.eventually_ne

-- DISSOLVED: HasDerivWithinAt.eventually_notMem

-- DISSOLVED: HasDerivAt.tendsto_nhdsNE

-- DISSOLVED: HasDerivAt.eventually_ne

-- DISSOLVED: HasDerivAt.eventually_notMem

theorem derivWithin_zero_of_frequently_const {c} (h : ∃ᶠ y in 𝓝[s \ {x}] x, f y = c) :
    derivWithin f s x = 0 := by
  by_cases hf : DifferentiableWithinAt 𝕜 f s x
  · contrapose! h
    exact hf.hasDerivWithinAt.eventually_ne h
  · exact derivWithin_zero_of_not_differentiableWithinAt hf

theorem derivWithin_zero_of_frequently_mem (t : Set F) (ht : ¬ AccPt (f x) (𝓟 t))
    (h : ∃ᶠ y in 𝓝[s \ {x}] x, f y ∈ t) : derivWithin f s x = 0 := by
  by_cases hf : DifferentiableWithinAt 𝕜 f s x
  · contrapose! h
    exact hf.hasDerivWithinAt.eventually_notMem h t ht
  · exact derivWithin_zero_of_not_differentiableWithinAt hf

theorem deriv_zero_of_frequently_const {c} (h : ∃ᶠ y in 𝓝[≠] x, f y = c) : deriv f x = 0 := by
  rw [← derivWithin_univ, derivWithin_zero_of_frequently_const]
  rwa [← compl_eq_univ_diff]

theorem deriv_zero_of_frequently_mem (t : Set F) (ht : ¬ AccPt (f x) (𝓟 t))
    (h : ∃ᶠ y in 𝓝[≠] x, f y ∈ t) : deriv f x = 0 := by
  rw [← derivWithin_univ, derivWithin_zero_of_frequently_mem t ht]
  rwa [← compl_eq_univ_diff]

theorem not_differentiableWithinAt_of_local_left_inverse_hasDerivWithinAt_zero {f g : 𝕜 → 𝕜} {a : 𝕜}
    {s t : Set 𝕜} (ha : a ∈ s) (hsu : UniqueDiffWithinAt 𝕜 s a) (hf : HasDerivWithinAt f 0 t (g a))
    (hst : MapsTo g s t) (hfg : f ∘ g =ᶠ[𝓝[s] a] id) : ¬DifferentiableWithinAt 𝕜 g s a := by
  intro hg
  have := (hf.comp a hg.hasDerivWithinAt hst).congr_of_eventuallyEq_of_mem hfg.symm ha
  simpa using hsu.eq_deriv _ this (hasDerivWithinAt_id _ _)

theorem not_differentiableAt_of_local_left_inverse_hasDerivAt_zero {f g : 𝕜 → 𝕜} {a : 𝕜}
    (hf : HasDerivAt f 0 (g a)) (hfg : f ∘ g =ᶠ[𝓝 a] id) : ¬DifferentiableAt 𝕜 g a := by
  intro hg
  have := (hf.comp a hg.hasDerivAt).congr_of_eventuallyEq hfg.symm
  simpa using this.unique (hasDerivAt_id a)
