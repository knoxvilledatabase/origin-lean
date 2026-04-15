/-
Extracted from NumberTheory/Padics/ProperSpace.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Properness of the p-adic numbers

In this file, we prove that `ℤ_[p]` is totally bounded and compact,
and that `ℚ_[p]` is proper.

## Main results

- `PadicInt.totallyBounded_univ` : The set of p-adic integers `ℤ_[p]` is totally bounded.
- `PadicInt.compactSpace` : The set of p-adic integers `ℤ_[p]` is a compact topological space.
- `Padic.instProperSpace` : The field of p-adic numbers `ℚ_[p]` is a proper metric space.

## Notation

- `p` : Is a natural prime.

## References

Gouvêa, F. Q. (2020) p-adic Numbers An Introduction. 3rd edition.
  Cham, Springer International Publishing
-/

assert_not_exists FiniteDimensional

open Metric Topology

variable (p : ℕ) [Fact (Nat.Prime p)]

namespace PadicInt

set_option backward.isDefEq.respectTransparency false in

theorem totallyBounded_univ : TotallyBounded (Set.univ : Set ℤ_[p]) := by
  refine Metric.totallyBounded_iff.mpr (fun ε hε ↦ ?_)
  obtain ⟨k, hk⟩ := exists_pow_neg_lt p hε
  refine ⟨Nat.cast '' Finset.range (p ^ k), Set.toFinite _, fun z _ ↦ ?_⟩
  simp only [PadicInt, Set.mem_iUnion, Metric.mem_ball, exists_prop, Set.exists_mem_image]
  refine ⟨z.appr k, ?_, ?_⟩
  · simpa only [Finset.mem_coe, Finset.mem_range] using z.appr_lt k
  · exact (((z - z.appr k).norm_le_pow_iff_mem_span_pow k).mpr (z.appr_spec k)).trans_lt hk

-- INSTANCE (free from Core): compactSpace

end PadicInt

namespace Padic

-- INSTANCE (free from Core): :

end Padic
