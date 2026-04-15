/-
Extracted from Analysis/Complex/CoveringMap.lean
Genuine: 2 of 11 | Dissolved: 9 | Infrastructure: 0
-/
import Origin.Core

/-!
# Covering maps involving the complex plane

In this file, we show that `Complex.exp` and `(· ^ n)` (for `n ≠ 0`) are a covering map on `{0}ᶜ`.
We also show that any complex polynomial is a covering map on the set of regular values.
-/

open Topology

namespace Complex

-- DISSOLVED: isAddQuotientCoveringMap_exp

-- DISSOLVED: isCoveringMap_exp

theorem isCoveringMapOn_exp : IsCoveringMapOn Complex.exp {0}ᶜ :=
  .of_isCoveringMap_subtype (by simp) _ isCoveringMap_exp

end Complex

open Polynomial

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]

theorem Polynomial.isCoveringMapOn_eval (p : 𝕜[X]) :
    IsCoveringMapOn p.eval (p.eval '' {k | p.derivative.eval k = 0})ᶜ := by
  refine p.isClosedMap_eval.isCoveringMapOn_of_openPartialHomeomorph (fun x hx ↦ ?_)
    fun x hx ↦ ⟨_, ((p.hasStrictDerivAt x).hasStrictFDerivAt_equiv
      fun h ↦ hx ⟨x, h, rfl⟩).mem_toOpenPartialHomeomorph_source, by simp⟩
  obtain rfl | ne := eq_or_ne p (C x)
  · simp at hx
  · simpa only [preimage_eval_singleton ne] using rootSet_finite ..

-- DISSOLVED: isCoveringMapOn_npow

-- DISSOLVED: isCoveringMap_npow

-- DISSOLVED: isCoveringMap_zpow

-- DISSOLVED: isCoveringMapOn_zpow

attribute [-instance] Units.mulAction'

-- DISSOLVED: isQuotientCoveringMap_npow

-- DISSOLVED: Complex.isQuotientCoveringMap_npow

-- DISSOLVED: isQuotientCoveringMap_zpow

end
