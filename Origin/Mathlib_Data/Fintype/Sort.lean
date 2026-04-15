/-
Extracted from Data/Fintype/Sort.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Sorting a finite type

This file provides two equivalences for linearly ordered fintypes:
* `monoEquivOfFin`: Order isomorphism between `α` and `Fin (card α)`.
* `finSumEquivOfFinset`: Equivalence between `α` and `Fin m ⊕ Fin n` where `m` and `n` are
  respectively the cardinalities of some `Finset α` and its complement.
-/

open Finset

def monoEquivOfFin (α : Type*) [Fintype α] [LinearOrder α] {k : ℕ} (h : Fintype.card α = k) :
    Fin k ≃o α :=
  (univ.orderIsoOfFin h).trans <| (OrderIso.setCongr _ _ coe_univ).trans OrderIso.Set.univ

variable {α : Type*} [DecidableEq α] [Fintype α] [LinearOrder α] {m n : ℕ} {s : Finset α}

def finSumEquivOfFinset (hm : #s = m) (hn : #sᶜ = n) : Fin m ⊕ Fin n ≃ α :=
  calc
    Fin m ⊕ Fin n ≃ (s : Set α) ⊕ (sᶜ : Set α) :=
      Equiv.sumCongr (s.orderIsoOfFin hm).toEquiv <|
        (sᶜ.orderIsoOfFin hn).toEquiv.trans <| Equiv.setCongr s.coe_compl
    _ ≃ α := Equiv.Set.sumCompl _
