/-
Extracted from Data/Int/Range.lean
Genuine: 2 of 6 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Intervals in ℤ

This file defines integer ranges. `range m n` is the set of integers greater than `m` and strictly
less than `n`.

## Note

This could be unified with `Data.List.Intervals`. See the TODOs there.
-/

namespace Int

def range (m n : ℤ) : List ℤ :=
  ((List.range (toNat (n - m))) : List ℕ).map fun (r : ℕ) => (m + r : ℤ)

theorem mem_range_iff {m n r : ℤ} : r ∈ range m n ↔ m ≤ r ∧ r < n := by
  simp only [range, List.mem_map, List.mem_range, lt_toNat, lt_sub_iff_add_lt, add_comm]
  exact ⟨fun ⟨a, ha⟩ => ha.2 ▸ ⟨le_add_of_nonneg_right (Int.natCast_nonneg _), ha.1⟩,
    fun h => ⟨toNat (r - m), by simp [toNat_of_nonneg (sub_nonneg.2 h.1), h.2] ⟩⟩

-- INSTANCE (free from Core): decidableLELT

-- INSTANCE (free from Core): decidableLELE

-- INSTANCE (free from Core): decidableLTLT

-- INSTANCE (free from Core): decidableLTLE

end Int
