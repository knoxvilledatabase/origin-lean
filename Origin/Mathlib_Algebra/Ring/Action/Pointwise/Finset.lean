/-
Extracted from Algebra/Ring/Action/Pointwise/Finset.lean
Genuine: 1 of 2 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core

/-!
# Pointwise actions on sets in a ring

This file proves properties of pointwise actions on sets in a ring.

## Tags

set multiplication, set addition, pointwise addition, pointwise multiplication,
pointwise subtraction
-/

open Module

open scoped Pointwise

variable {R G M : Type*}

namespace Finset

section Semiring

variable [Semiring R] [IsDomain R] [AddCommMonoid M] [DecidableEq M] [Module R M]
  [IsTorsionFree R M] {s : Finset R} {t : Finset M} {r : R} {m : M}

-- DISSOLVED: zero_mem_smul_finset_iff

lemma zero_mem_smul_iff : (0 : M) ∈ s • t ↔ 0 ∈ s ∧ t.Nonempty ∨ 0 ∈ t ∧ s.Nonempty := by
  rw [← mem_coe, coe_smul, Set.zero_mem_smul_iff]; rfl

end Semiring

variable [Ring R] [AddCommGroup G] [Module R G] [DecidableEq G] {s : Finset R} {t : Finset G}
  {a : R}
