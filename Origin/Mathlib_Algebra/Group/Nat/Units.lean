/-
Extracted from Algebra/Group/Nat/Units.lean
Genuine: 4 of 6 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# The unit of the natural numbers
-/

assert_not_exists MonoidWithZero DenselyOrdered

namespace Nat

/-! #### Units -/

lemma units_eq_one (u : ℕˣ) : u = 1 := Units.ext <| Nat.eq_one_of_dvd_one ⟨u.inv, u.val_inv.symm⟩

lemma addUnits_eq_zero (u : AddUnits ℕ) : u = 0 :=
  AddUnits.ext <| (Nat.eq_zero_of_add_eq_zero u.val_neg).1

-- INSTANCE (free from Core): unique_units

-- INSTANCE (free from Core): unique_addUnits

protected lemma isUnit_iff {n : ℕ} : IsUnit n ↔ n = 1 := isUnit_iff_eq_one

protected lemma isAddUnit_iff {n : ℕ} : IsAddUnit n ↔ n = 0 := isAddUnit_iff_eq_zero

end Nat
