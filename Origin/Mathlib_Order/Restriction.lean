/-
Extracted from Order/Restriction.lean
Genuine: 4 | Conflates: 0 | Dissolved: 0 | Infrastructure: 8
-/
import Origin.Core
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Order.Interval.Finset.Basic

/-!
# Restriction of a function indexed by a preorder

Given a preorder `α` and dependent function `f : (i : α) → π i` and `a : α`, one might want
to consider the restriction of `f` to elements `≤ a`.
This is defined in this file as `Preorder.restrictLe a f`.
Similarly, if we have `a b : α`, `hab : a ≤ b` and `f : (i : ↑(Set.Iic b)) → π ↑i`,
one might want to restrict it to elements `≤ a`.
This is defined in this file as `Preorder.restrictLe₂ hab f`.

We also provide versions where the intervals are seen as finite sets, see `Preorder.frestrictLe`
and `Preorder.frestrictLe₂`.

## Main definitions
* `Preorder.restrictLe a f`: Restricts the function `f` to the variables indexed by elements `≤ a`.
-/

namespace Preorder

variable {α : Type*} [Preorder α] {π : α → Type*}

section Set

open Set

def restrictLe (a : α) := (Iic a).restrict (π := π)

@[simp]
lemma restrictLe_apply (a : α) (f : (a : α) → π a) (i : Iic a) : restrictLe a f i = f i := rfl

def restrictLe₂ {a b : α} (hab : a ≤ b) := Set.restrict₂ (π := π) (Iic_subset_Iic.2 hab)

@[simp]
lemma restrictLe₂_apply {a b : α} (hab : a ≤ b) (f : (i : Iic b) → π i) (i : Iic a) :
    restrictLe₂ hab f i = f ⟨i.1, Iic_subset_Iic.2 hab i.2⟩ := rfl

theorem restrictLe₂_comp_restrictLe {a b : α} (hab : a ≤ b) :
    (restrictLe₂ (π := π) hab) ∘ (restrictLe b) = restrictLe a := rfl

theorem restrictLe₂_comp_restrictLe₂ {a b c : α} (hab : a ≤ b) (hbc : b ≤ c) :
    (restrictLe₂ (π := π) hab) ∘ (restrictLe₂ hbc) = restrictLe₂ (hab.trans hbc) := rfl

end Set

section Finset

variable [LocallyFiniteOrderBot α]

open Finset

def frestrictLe (a : α) := (Iic a).restrict (π := π)

@[simp]
lemma frestrictLe_apply (a : α) (f : (a : α) → π a) (i : Iic a) : frestrictLe a f i = f i := rfl

def frestrictLe₂ {a b : α} (hab : a ≤ b) := Finset.restrict₂ (π := π) (Iic_subset_Iic.2 hab)

@[simp]
lemma frestrictLe₂_apply {a b : α} (hab : a ≤ b) (f : (i : Iic b) → π i) (i : Iic a) :
    frestrictLe₂ hab f i = f ⟨i.1, Iic_subset_Iic.2 hab i.2⟩ := rfl

theorem frestrictLe₂_comp_frestrictLe {a b : α} (hab : a ≤ b) :
    (frestrictLe₂ (π := π) hab) ∘ (frestrictLe b) = frestrictLe a := rfl

theorem frestrictLe₂_comp_frestrictLe₂ {a b c : α} (hab : a ≤ b) (hbc : b ≤ c) :
    (frestrictLe₂ (π := π) hab) ∘ (frestrictLe₂ hbc) = frestrictLe₂ (hab.trans hbc) := rfl

end Finset

end Preorder
