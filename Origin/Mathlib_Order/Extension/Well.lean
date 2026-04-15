/-
Extracted from Order/Extension/Well.lean
Genuine: 7 | Conflates: 0 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core
import Mathlib.Data.Prod.Lex
import Mathlib.SetTheory.Ordinal.Rank

/-!
# Extend a well-founded order to a well-order

This file constructs a well-order (linear well-founded order) which is an extension of a given
well-founded order.

## Proof idea

We can map our order into two well-orders:
* the first map respects the order but isn't necessarily injective. Namely, this is the *rank*
  function `IsWellFounded.rank : α → Ordinal`.
* the second map is injective but doesn't necessarily respect the order. This is an arbitrary
  embedding into `Cardinal` given by `embeddingToCardinal`.

Then their lexicographic product is a well-founded linear order which our original order injects in.

## Porting notes

The definition in `mathlib` 3 used an auxiliary well-founded order on `α` lifted from `Cardinal`
instead of `Cardinal`. The new definition is definitionally equal to the `mathlib` 3 version but
avoids non-standard instances.

## Tags

well founded relation, well order, extension
-/

universe u

variable {α : Type u} {r : α → α → Prop}

namespace IsWellFounded

variable {α : Type u} (r : α → α → Prop) [IsWellFounded α r]

noncomputable def wellOrderExtension : LinearOrder α :=
  @LinearOrder.lift' α (Ordinal ×ₗ Cardinal) _ (fun a : α => (rank r a, embeddingToCardinal a))
    fun _ _ h => embeddingToCardinal.injective <| congr_arg Prod.snd h

instance wellOrderExtension.isWellFounded_lt : IsWellFounded α (wellOrderExtension r).lt :=
  ⟨InvImage.wf (fun a : α => (rank r a, embeddingToCardinal a)) <|
    Ordinal.lt_wf.prod_lex Cardinal.lt_wf⟩

instance wellOrderExtension.isWellOrder_lt : IsWellOrder α (wellOrderExtension r).lt where

theorem exists_well_order_ge : ∃ s, r ≤ s ∧ IsWellOrder α s :=
  ⟨(wellOrderExtension r).lt, fun _ _ h => Prod.Lex.left _ _ (rank_lt_of_rel h), ⟨⟩⟩

end IsWellFounded

namespace WellFounded

set_option linter.deprecated false

variable (hwf : WellFounded r)

noncomputable def wellOrderExtension : LinearOrder α :=
  @LinearOrder.lift' α (Ordinal ×ₗ Cardinal) _ (fun a : α => (hwf.rank a, embeddingToCardinal a))
    fun _ _ h => embeddingToCardinal.injective <| congr_arg Prod.snd h

instance wellOrderExtension.isWellFounded_lt : IsWellFounded α hwf.wellOrderExtension.lt :=
  ⟨InvImage.wf (fun a : α => (hwf.rank a, embeddingToCardinal a)) <|
    Ordinal.lt_wf.prod_lex Cardinal.lt_wf⟩

include hwf in

theorem exists_well_order_ge : ∃ s, r ≤ s ∧ IsWellOrder α s :=
  ⟨hwf.wellOrderExtension.lt, fun _ _ h => Prod.Lex.left _ _ (hwf.rank_lt_of_rel h), ⟨⟩⟩

end WellFounded

def WellOrderExtension (α : Type*) : Type _ := α

instance [Inhabited α] : Inhabited (WellOrderExtension α) := ‹_›

def toWellOrderExtension : α ≃ WellOrderExtension α :=
  Equiv.refl _

noncomputable instance [LT α] [h : WellFoundedLT α] : LinearOrder (WellOrderExtension α) :=
  h.wellOrderExtension

instance WellOrderExtension.wellFoundedLT [LT α] [WellFoundedLT α] :
    WellFoundedLT (WellOrderExtension α) :=
  IsWellFounded.wellOrderExtension.isWellFounded_lt (α := α) (· < ·)

theorem toWellOrderExtension_strictMono [Preorder α] [WellFoundedLT α] :
    StrictMono (toWellOrderExtension : α → WellOrderExtension α) := fun _ _ h =>
  Prod.Lex.left _ _ <| IsWellFounded.rank_lt_of_rel h
