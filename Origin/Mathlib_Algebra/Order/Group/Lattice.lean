/-
Extracted from Algebra/Order/Group/Lattice.lean
Genuine: 13 of 13 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Algebra.Order.Group.OrderIso

/-!
# Lattice ordered groups

Lattice ordered groups were introduced by [Birkhoff][birkhoff1942]. They form the algebraic
underpinnings of vector lattices, Banach lattices, AL-space, AM-space etc.

A lattice ordered group is a type `α` satisfying:
* `Lattice α`
* `CommGroup α`
* `MulLeftMono α`
* `MulRightMono α`

This file establishes basic properties of lattice ordered groups. It is shown that when the group is
commutative, the lattice is distributive. This also holds in the non-commutative case
([Birkhoff][birkhoff1942],[Fuchs][fuchs1963]) but we do not yet have the machinery to establish this
in mathlib.

## References

* [Birkhoff, Lattice-ordered Groups][birkhoff1942]
* [Bourbaki, Algebra II][bourbaki1981]
* [Fuchs, Partially Ordered Algebraic Systems][fuchs1963]
* [Zaanen, Lectures on "Riesz Spaces"][zaanen1966]
* [Banasiak, Banach Lattices in Applications][banasiak]

## Tags

lattice, order, group
-/

open Function

variable {α : Type*}

section Group

variable [Lattice α] [Group α]

@[to_additive]
lemma mul_sup [MulLeftMono α] (a b c : α) :
    c * (a ⊔ b) = c * a ⊔ c * b :=
  (OrderIso.mulLeft _).map_sup _ _

@[to_additive]
lemma sup_mul [MulRightMono α] (a b c : α) :
    (a ⊔ b) * c = a * c ⊔ b * c :=
  (OrderIso.mulRight _).map_sup _ _

@[to_additive]
lemma mul_inf [MulLeftMono α] (a b c : α) :
    c * (a ⊓ b) = c * a ⊓ c * b :=
  (OrderIso.mulLeft _).map_inf _ _

@[to_additive]
lemma inf_mul [MulRightMono α] (a b c : α) :
    (a ⊓ b) * c = a * c ⊓ b * c :=
  (OrderIso.mulRight _).map_inf _ _

@[to_additive]
lemma sup_div [MulRightMono α] (a b c : α) :
    (a ⊔ b) / c = a / c ⊔ b / c :=
  (OrderIso.divRight _).map_sup _ _

@[to_additive]
lemma inf_div [MulRightMono α] (a b c : α) :
    (a ⊓ b) / c = a / c ⊓ b / c :=
  (OrderIso.divRight _).map_inf _ _

section

variable [MulLeftMono α] [MulRightMono α]

@[to_additive] lemma inv_sup (a b : α) : (a ⊔ b)⁻¹ = a⁻¹ ⊓ b⁻¹ := (OrderIso.inv α).map_sup _ _

@[to_additive] lemma inv_inf (a b : α) : (a ⊓ b)⁻¹ = a⁻¹ ⊔ b⁻¹ := (OrderIso.inv α).map_inf _ _

@[to_additive]
lemma div_sup (a b c : α) : c / (a ⊔ b) = c / a ⊓ c / b := (OrderIso.divLeft c).map_sup _ _

@[to_additive]
lemma div_inf (a b c : α) : c / (a ⊓ b) = c / a ⊔ c / b := (OrderIso.divLeft c).map_inf _ _

@[to_additive]
lemma pow_two_semiclosed
    {a : α} (ha : 1 ≤ a ^ 2) : 1 ≤ a := by
  suffices this : (a ⊓ 1) * (a ⊓ 1) = a ⊓ 1 by
    rwa [← inf_eq_right, ← mul_right_eq_self]
  rw [mul_inf, inf_mul, ← pow_two, mul_one, one_mul, inf_assoc, inf_left_idem, inf_comm,
    inf_assoc, inf_of_le_left ha]

end

end Group

variable [Lattice α] [CommGroup α]

@[to_additive]
lemma inf_mul_sup [MulLeftMono α] (a b : α) : (a ⊓ b) * (a ⊔ b) = a * b :=
  calc
    (a ⊓ b) * (a ⊔ b) = (a ⊓ b) * (a * b * (b⁻¹ ⊔ a⁻¹)) := by
      rw [mul_sup b⁻¹ a⁻¹ (a * b), mul_inv_cancel_right, mul_inv_cancel_comm]
    _ = (a ⊓ b) * (a * b * (a ⊓ b)⁻¹) := by rw [inv_inf, sup_comm]
    _ = a * b := by rw [mul_comm, inv_mul_cancel_right]

@[to_additive "Every lattice ordered commutative additive group is a distributive lattice"]
def CommGroup.toDistribLattice (α : Type*) [Lattice α] [CommGroup α]
    [MulLeftMono α] : DistribLattice α where
  le_sup_inf x y z := by
    rw [← mul_le_mul_iff_left (x ⊓ (y ⊓ z)), inf_mul_sup x (y ⊓ z), ← inv_mul_le_iff_le_mul,
      le_inf_iff]
    constructor
    · rw [inv_mul_le_iff_le_mul, ← inf_mul_sup x y]
      exact mul_le_mul' (inf_le_inf_left _ inf_le_left) inf_le_left
    · rw [inv_mul_le_iff_le_mul, ← inf_mul_sup x z]
      exact mul_le_mul' (inf_le_inf_left _ inf_le_right) inf_le_right
