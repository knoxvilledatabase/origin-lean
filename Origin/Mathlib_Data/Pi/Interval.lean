/-
Extracted from Data/Pi/Interval.lean
Genuine: 9 of 14 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-!
# Intervals in a pi type

This file shows that (dependent) functions to locally finite orders equipped with the pointwise
order are locally finite and calculates the cardinality of their intervals.
-/

open Finset Fintype

variable {ι : Type*} {α : ι → Type*} [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (α i)]

namespace Pi

section PartialOrder

variable [∀ i, PartialOrder (α i)]

section LocallyFiniteOrder

variable [∀ i, LocallyFiniteOrder (α i)]

-- INSTANCE (free from Core): instLocallyFiniteOrder

variable (a b : ∀ i, α i)

theorem card_Icc : #(Icc a b) = ∏ i, #(Icc (a i) (b i)) :=
  card_piFinset _

theorem card_Ico : #(Ico a b) = ∏ i, #(Icc (a i) (b i)) - 1 := by
  rw [card_Ico_eq_card_Icc_sub_one, card_Icc]

theorem card_Ioc : #(Ioc a b) = ∏ i, #(Icc (a i) (b i)) - 1 := by
  rw [card_Ioc_eq_card_Icc_sub_one, card_Icc]

theorem card_Ioo : #(Ioo a b) = ∏ i, #(Icc (a i) (b i)) - 2 := by
  rw [card_Ioo_eq_card_Icc_sub_two, card_Icc]

end LocallyFiniteOrder

section LocallyFiniteOrderBot

variable [∀ i, LocallyFiniteOrderBot (α i)] (b : ∀ i, α i)

-- INSTANCE (free from Core): instLocallyFiniteOrderBot

lemma card_Iic : #(Iic b) = ∏ i, #(Iic (b i)) := card_piFinset _

lemma card_Iio : #(Iio b) = ∏ i, #(Iic (b i)) - 1 := by rw [card_Iio_eq_card_Iic_sub_one, card_Iic]

end LocallyFiniteOrderBot

section LocallyFiniteOrderTop

variable [∀ i, LocallyFiniteOrderTop (α i)] (a : ∀ i, α i)

-- INSTANCE (free from Core): instLocallyFiniteOrderTop

lemma card_Ici : #(Ici a) = ∏ i, #(Ici (a i)) := card_piFinset _

lemma card_Ioi : #(Ioi a) = ∏ i, #(Ici (a i)) - 1 := by rw [card_Ioi_eq_card_Ici_sub_one, card_Ici]

end LocallyFiniteOrderTop

end PartialOrder

section Lattice

variable [∀ i, Lattice (α i)] [∀ i, LocallyFiniteOrder (α i)] (a b : ∀ i, α i)

theorem card_uIcc : #(uIcc a b) = ∏ i, #(uIcc (a i) (b i)) := card_Icc _ _

end Lattice

end Pi
