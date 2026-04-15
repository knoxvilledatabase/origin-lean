/-
Extracted from Analysis/Calculus/Deriv/Inverse.lean
Genuine: 2 | Conflates: 0 | Dissolved: 8 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Equiv

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

variable {x : 𝕜}

-- DISSOLVED: HasStrictDerivAt.hasStrictFDerivAt_equiv

-- DISSOLVED: HasDerivAt.hasFDerivAt_equiv

-- DISSOLVED: HasStrictDerivAt.of_local_left_inverse

-- DISSOLVED: PartialHomeomorph.hasStrictDerivAt_symm

-- DISSOLVED: HasDerivAt.of_local_left_inverse

-- DISSOLVED: PartialHomeomorph.hasDerivAt_symm

-- DISSOLVED: HasDerivAt.eventually_ne

-- DISSOLVED: HasDerivAt.tendsto_punctured_nhds

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
