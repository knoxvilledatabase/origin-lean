/-
Extracted from Data/Fintype/Shrink.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.Data.Countable.Small
import Mathlib.Data.Fintype.Card

/-!
# Fintype instance for `Shrink`
-/

universe u v

variable {α : Type u} [Fintype α]

noncomputable instance Shrink.instFintype : Fintype (Shrink.{v} α) := .ofEquiv _ (equivShrink _)

instance Shrink.instFinite {α : Type u} [Finite α] : Finite (Shrink.{v} α) :=
  .of_equiv _ (equivShrink _)

@[simp] lemma Fintype.card_shrink [Fintype (Shrink.{v} α)] : card (Shrink.{v} α) = card α :=
  card_congr (equivShrink _).symm
