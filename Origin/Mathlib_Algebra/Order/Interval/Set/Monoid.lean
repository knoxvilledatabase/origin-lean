/-
Extracted from Algebra/Order/Interval/Set/Monoid.lean
Genuine: 6 of 6 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Images of intervals under `(+ d)`

The lemmas in this file state that addition maps intervals bijectively. The typeclass
`ExistsAddOfLE` is defined specifically to make them work when combined with
`OrderedCancelAddCommMonoid`; the lemmas below therefore apply to all
`OrderedAddCommGroup`, but also to `ℕ` and `ℝ≥0`, which are not groups.
-/

namespace Set

variable {M : Type*} [AddCommMonoid M] [PartialOrder M] [IsOrderedCancelAddMonoid M]
  [ExistsAddOfLE M] (a b c d : M)

theorem Ici_add_bij : BijOn (· + d) (Ici a) (Ici (a + d)) := by
  refine ⟨by simp [MapsTo], by simp, fun _ h => ?_⟩
  obtain ⟨c, rfl⟩ := exists_add_of_le (mem_Ici.mp h)
  rw [mem_Ici, add_right_comm, add_le_add_iff_right] at h
  exact ⟨a + c, h, by rw [add_right_comm]⟩

theorem Ioi_add_bij : BijOn (· + d) (Ioi a) (Ioi (a + d)) := by
  refine ⟨by simp [MapsTo], by simp, fun _ h => ?_⟩
  obtain ⟨c, rfl⟩ := exists_add_of_le (mem_Ioi.mp h).le
  rw [mem_Ioi, add_right_comm, add_lt_add_iff_right] at h
  exact ⟨a + c, h, by rw [add_right_comm]⟩

theorem Icc_add_bij : BijOn (· + d) (Icc a b) (Icc (a + d) (b + d)) := by
  rw [← Ici_inter_Iic, ← Ici_inter_Iic]
  exact (Ici_add_bij a d).inter_mapsTo (by simp [MapsTo]) fun x hx => le_of_add_le_add_right hx.2

theorem Ioo_add_bij : BijOn (· + d) (Ioo a b) (Ioo (a + d) (b + d)) := by
  rw [← Ioi_inter_Iio, ← Ioi_inter_Iio]
  exact (Ioi_add_bij a d).inter_mapsTo (by simp [MapsTo]) fun x hx => lt_of_add_lt_add_right hx.2

theorem Ioc_add_bij : BijOn (· + d) (Ioc a b) (Ioc (a + d) (b + d)) := by
  rw [← Ioi_inter_Iic, ← Ioi_inter_Iic]
  exact (Ioi_add_bij a d).inter_mapsTo (by simp [MapsTo]) fun x hx => le_of_add_le_add_right hx.2

theorem Ico_add_bij : BijOn (· + d) (Ico a b) (Ico (a + d) (b + d)) := by
  rw [← Ici_inter_Iio, ← Ici_inter_Iio]
  exact (Ici_add_bij a d).inter_mapsTo (by simp [MapsTo]) fun x hx => lt_of_add_lt_add_right hx.2

/-!
### Images under `x ↦ x + a`
-/
