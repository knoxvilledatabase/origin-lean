/-
Extracted from LinearAlgebra/Dimension/Torsion/Finite.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Results relating rank and torsion.

-/

variable {R M : Type*} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]

lemma rank_eq_zero_iff_isTorsion : Module.rank R M = 0 ↔ Module.IsTorsion R M := by
  rw [Module.IsTorsion, rank_eq_zero_iff]
  simp [mem_nonZeroDivisors_iff_ne_zero]

theorem Module.finrank_eq_zero_iff_isTorsion [StrongRankCondition R] [Module.Finite R M] :
    finrank R M = 0 ↔ Module.IsTorsion R M := by
  rw [← rank_eq_zero_iff_isTorsion (R := R), ← finrank_eq_rank]
  norm_cast
