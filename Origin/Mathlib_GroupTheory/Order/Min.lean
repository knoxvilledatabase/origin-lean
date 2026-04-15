/-
Extracted from GroupTheory/Order/Min.lean
Genuine: 6 | Conflates: 1 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.GroupTheory.Torsion

/-!
# Minimum order of an element

This file defines the minimum order of an element of a monoid.

## Main declarations

* `Monoid.minOrder`: The minimum order of an element of a given monoid.
* `Monoid.minOrder_eq_top`: The minimum order is infinite iff the monoid is torsion-free.
* `ZMod.minOrder`: The minimum order of $$ℤ/nℤ$$ is the smallest factor of `n`, unless `n = 0, 1`.
-/

open Subgroup

variable {α : Type*}

namespace Monoid

section Monoid

variable (α) [Monoid α]

-- CONFLATES (assumes ground = zero): minOrder
@[to_additive "The minimum order of a non-identity element. Also the minimum size of a nontrivial
subgroup, see `AddMonoid.le_minOrder_iff_forall_addSubgroup`. Returns `∞` if the monoid is
torsion-free."]
noncomputable def minOrder : ℕ∞ := ⨅ (a : α) (_ha : a ≠ 1) (_ha' : IsOfFinOrder a), orderOf a

variable {α} {a : α}

@[to_additive (attr := simp)]
lemma minOrder_eq_top : minOrder α = ⊤ ↔ IsTorsionFree α := by simp [minOrder, IsTorsionFree]

@[to_additive (attr := simp)] protected alias ⟨_, IsTorsionFree.minOrder⟩ := minOrder_eq_top
@[to_additive (attr := simp)]
lemma le_minOrder {n : ℕ∞} :
    n ≤ minOrder α ↔ ∀ ⦃a : α⦄, a ≠ 1 → IsOfFinOrder a → n ≤ orderOf a := by simp [minOrder]

@[to_additive]
lemma minOrder_le_orderOf (ha : a ≠ 1) (ha' : IsOfFinOrder a) : minOrder α ≤ orderOf a :=
  le_minOrder.1 le_rfl ha ha'

end Monoid

variable [Group α] {s : Subgroup α}

@[to_additive]
lemma le_minOrder_iff_forall_subgroup {n : ℕ∞} :
    n ≤ minOrder α ↔ ∀ ⦃s : Subgroup α⦄, s ≠ ⊥ → (s : Set α).Finite → n ≤ Nat.card s := by
  rw [le_minOrder]
  refine ⟨fun h s hs hs' ↦ ?_, fun h a ha ha' ↦ ?_⟩
  · obtain ⟨a, has, ha⟩ := s.bot_or_exists_ne_one.resolve_left hs
    exact
      (h ha <| finite_zpowers.1 <| hs'.subset <| zpowers_le.2 has).trans
        (WithTop.coe_le_coe.2 <| s.orderOf_le_card hs' has)
  · simpa using h (zpowers_ne_bot.2 ha) ha'.finite_zpowers

@[to_additive]
lemma minOrder_le_natCard (hs : s ≠ ⊥) (hs' : (s : Set α).Finite) : minOrder α ≤ Nat.card s :=
  le_minOrder_iff_forall_subgroup.1 le_rfl hs hs'

end Monoid

open AddMonoid AddSubgroup Nat Set

namespace ZMod

-- DISSOLVED: minOrder

@[simp]
lemma minOrder_of_prime {p : ℕ} (hp : p.Prime) : minOrder (ZMod p) = p := by
  rw [ZMod.minOrder hp.ne_zero hp.ne_one, hp.minFac_eq]

end ZMod
