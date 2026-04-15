/-
Extracted from Order/Compare.lean
Genuine: 14 of 14 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Comparison

This file provides basic results about orderings and comparison in linear orders.


## Definitions

* `CmpLE`: An `Ordering` from `≤`.
* `Ordering.Compares`: Turns an `Ordering` into `<` and `=` propositions.
* `linearOrderOfCompares`: Constructs a `LinearOrder` instance from the fact that any two
  elements that are not one strictly less than the other either way are equal.
-/

variable {α β : Type*}

def cmpLE {α} [LE α] [DecidableLE α] (x y : α) : Ordering :=
  if x ≤ y then if y ≤ x then Ordering.eq else Ordering.lt else Ordering.gt

theorem cmpLE_swap {α} [LE α] [@Std.Total α (· ≤ ·)] [DecidableLE α] (x y : α) :
    (cmpLE x y).swap = cmpLE y x := by
  by_cases xy : x ≤ y <;> by_cases yx : y ≤ x <;> simp [cmpLE, *, Ordering.swap]
  cases not_or_intro xy yx (total_of _ _ _)

theorem cmpLE_eq_cmp {α} [Preorder α] [@Std.Total α (· ≤ ·)] [DecidableLE α] [DecidableLT α]
    (x y : α) : cmpLE x y = cmp x y := by
  by_cases xy : x ≤ y <;> by_cases yx : y ≤ x <;> simp [cmpLE, lt_iff_le_not_ge, *, cmp, cmpUsing]
  cases not_or_intro xy yx (total_of _ _ _)

namespace Ordering

theorem compares_swap [LT α] {a b : α} {o : Ordering} : o.swap.Compares a b ↔ o.Compares b a := by
  cases o
  · exact Iff.rfl
  · exact eq_comm
  · exact Iff.rfl

alias ⟨Compares.of_swap, Compares.swap⟩ := compares_swap

theorem swap_eq_iff_eq_swap {o o' : Ordering} : o.swap = o' ↔ o = o'.swap := by
  rw [← swap_inj, swap_swap]

theorem Compares.eq_lt [Preorder α] : ∀ {o} {a b : α}, Compares o a b → (o = lt ↔ a < b)
  | lt, _, _, h => ⟨fun _ => h, fun _ => rfl⟩
  | eq, a, b, h => ⟨fun h => by injection h, fun h' => (ne_of_lt h' h).elim⟩
  | gt, a, b, h => ⟨fun h => by injection h, fun h' => (lt_asymm h h').elim⟩

theorem Compares.ne_lt [Preorder α] : ∀ {o} {a b : α}, Compares o a b → (o ≠ lt ↔ b ≤ a)
  | lt, _, _, h => ⟨absurd rfl, fun h' => (not_le_of_gt h h').elim⟩
  | eq, _, _, h => ⟨fun _ => ge_of_eq h, fun _ h => by injection h⟩
  | gt, _, _, h => ⟨fun _ => le_of_lt h, fun _ h => by injection h⟩

theorem Compares.eq_eq [Preorder α] : ∀ {o} {a b : α}, Compares o a b → (o = eq ↔ a = b)
  | lt, a, b, h => ⟨fun h => by injection h, fun h' => (ne_of_lt h h').elim⟩
  | eq, _, _, h => ⟨fun _ => h, fun _ => rfl⟩
  | gt, a, b, h => ⟨fun h => by injection h, fun h' => (ne_of_gt h h').elim⟩

theorem Compares.eq_gt [Preorder α] {o} {a b : α} (h : Compares o a b) : o = gt ↔ b < a :=
  swap_eq_iff_eq_swap.symm.trans h.swap.eq_lt

theorem Compares.ne_gt [Preorder α] {o} {a b : α} (h : Compares o a b) : o ≠ gt ↔ a ≤ b :=
  (not_congr swap_eq_iff_eq_swap.symm).trans h.swap.ne_lt

theorem Compares.le_total [Preorder α] {a b : α} : ∀ {o}, Compares o a b → a ≤ b ∨ b ≤ a
  | lt, h => Or.inl (le_of_lt h)
  | eq, h => Or.inl (le_of_eq h)
  | gt, h => Or.inr (le_of_lt h)

theorem Compares.le_antisymm [Preorder α] {a b : α} : ∀ {o}, Compares o a b → a ≤ b → b ≤ a → a = b
  | lt, h, _, hba => (not_le_of_gt h hba).elim
  | eq, h, _, _ => h
  | gt, h, hab, _ => (not_le_of_gt h hab).elim

theorem Compares.inj [Preorder α] {o₁} :
    ∀ {o₂} {a b : α}, Compares o₁ a b → Compares o₂ a b → o₁ = o₂
  | lt, _, _, h₁, h₂ => h₁.eq_lt.2 h₂
  | eq, _, _, h₁, h₂ => h₁.eq_eq.2 h₂
  | gt, _, _, h₁, h₂ => h₁.eq_gt.2 h₂

theorem compares_iff_of_compares_impl [LinearOrder α] [Preorder β] {a b : α} {a' b' : β}
    (h : ∀ {o}, Compares o a b → Compares o a' b') (o) : Compares o a b ↔ Compares o a' b' := by
  refine ⟨h, fun ho => ?_⟩
  rcases lt_trichotomy a b with hab | hab | hab
  · have hab : Compares Ordering.lt a b := hab
    rwa [ho.inj (h hab)]
  · have hab : Compares Ordering.eq a b := hab
    rwa [ho.inj (h hab)]
  · have hab : Compares Ordering.gt a b := hab
    rwa [ho.inj (h hab)]

end Ordering

open Ordering OrderDual
