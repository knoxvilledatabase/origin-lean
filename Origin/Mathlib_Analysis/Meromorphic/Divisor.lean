/-
Extracted from Analysis/Meromorphic/Divisor.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# The Divisor of a meromorphic function

This file defines the divisor of a meromorphic function and proves the most basic lemmas about those
divisors. The lemma `MeromorphicOn.divisor_restrict` guarantees compatibility between restrictions
of divisors and of meromorphic functions to subsets of their domain of definition.
-/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {U : Set 𝕜} {z : 𝕜}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

open Filter Topology

namespace MeromorphicOn

/-!
## Definition of the Divisor
-/

open Classical in

noncomputable def divisor (f : 𝕜 → E) (U : Set 𝕜) :
    Function.locallyFinsuppWithin U ℤ where
  toFun := fun z ↦ if MeromorphicOn f U ∧ z ∈ U then (meromorphicOrderAt f z).untop₀ else 0
  supportWithinDomain' z hz := by
    by_contra h₂z
    simp [h₂z] at hz
  supportLocallyFiniteWithinDomain' := by
    simp_all only [Function.support_subset_iff, ne_eq, ite_eq_right_iff, WithTop.untop₀_eq_zero,
      and_imp, Classical.not_imp, not_or, implies_true,
      ← supportDiscreteWithin_iff_locallyFiniteWithin]
    by_cases hf : MeromorphicOn f U
    · filter_upwards [mem_codiscrete_subtype_iff_mem_codiscreteWithin.1
        hf.codiscrete_setOf_meromorphicOrderAt_eq_zero_or_top]
      simp only [Set.mem_image, Set.mem_setOf_eq, Subtype.exists, exists_and_left, exists_prop,
        exists_eq_right_right, Pi.ofNat_apply, ite_eq_right_iff, WithTop.untop₀_eq_zero, and_imp]
      tauto
    · simp [hf, Pi.zero_def]

open Classical in
