/-
Extracted from Order/Restriction.lean
Genuine: 4 | Conflates: 0 | Dissolved: 0 | Infrastructure: 8
-/
import Origin.Core
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Order.Interval.Finset.Basic

noncomputable section

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

def restrictLe₂ {a b : α} (hab : a ≤ b) := Set.restrict₂ (π := π) (Iic_subset_Iic.2 hab)

end Set

section Finset

variable [LocallyFiniteOrderBot α]

open Finset

def frestrictLe (a : α) := (Iic a).restrict (π := π)

def frestrictLe₂ {a b : α} (hab : a ≤ b) := Finset.restrict₂ (π := π) (Iic_subset_Iic.2 hab)

end Finset

end Preorder
