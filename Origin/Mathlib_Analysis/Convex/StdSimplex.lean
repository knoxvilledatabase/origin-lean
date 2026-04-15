/-
Extracted from Analysis/Convex/StdSimplex.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The standard simplex

In this file, given an ordered semiring `𝕜` and a finite type `ι`,
we define `stdSimplex : Set (ι → 𝕜)` as the set of vectors with non-negative
coordinates with total sum `1`.

When `f : X → Y` is a map between finite types, we define the map
`stdSimplex.map f : stdSimplex 𝕜 X → stdSimplex 𝕜 Y`.

-/

open Set Convex Bornology

section OrderedSemiring

variable (𝕜) (ι : Type*) [Semiring 𝕜] [PartialOrder 𝕜] [Fintype ι]

def stdSimplex : Set (ι → 𝕜) :=
  { f | (∀ x, 0 ≤ f x) ∧ ∑ x, f x = 1 }

theorem stdSimplex_eq_inter : stdSimplex 𝕜 ι = (⋂ x, { f | 0 ≤ f x }) ∩ { f | ∑ x, f x = 1 } := by
  ext f
  simp only [stdSimplex, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]

theorem convex_stdSimplex [IsOrderedRing 𝕜] : Convex 𝕜 (stdSimplex 𝕜 ι) := by
  refine fun f hf g hg a b ha hb hab => ⟨fun x => ?_, ?_⟩
  · apply_rules [add_nonneg, mul_nonneg, hf.1, hg.1]
  · simp_rw [Pi.add_apply, Pi.smul_apply]
    rwa [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum, hf.2, hg.2, smul_eq_mul,
      smul_eq_mul, mul_one, mul_one]
