/-
Extracted from Data/Sigma/Interval.lean
Genuine: 4 of 5 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Finite intervals in a sigma type

This file provides the `LocallyFiniteOrder` instance for the disjoint sum of orders `Σ i, α i` and
calculates the cardinality of its finite intervals.

## TODO

Do the same for the lexicographical order
-/

open Finset Function

namespace Sigma

variable {ι : Type*} {α : ι → Type*}

/-! ### Disjoint sum of orders -/

section Disjoint

section LocallyFiniteOrder

variable [DecidableEq ι] [∀ i, Preorder (α i)] [∀ i, LocallyFiniteOrder (α i)]

-- INSTANCE (free from Core): instLocallyFiniteOrder

variable (a b : Σ i, α i)

theorem card_Icc : #(Icc a b) = if h : a.1 = b.1 then #(Icc (h.rec a.2) b.2) else 0 :=
  card_sigmaLift (fun _ => Icc) _ _

theorem card_Ico : #(Ico a b) = if h : a.1 = b.1 then #(Ico (h.rec a.2) b.2) else 0 :=
  card_sigmaLift (fun _ => Ico) _ _

theorem card_Ioc : #(Ioc a b) = if h : a.1 = b.1 then #(Ioc (h.rec a.2) b.2) else 0 :=
  card_sigmaLift (fun _ => Ioc) _ _

theorem card_Ioo : #(Ioo a b) = if h : a.1 = b.1 then #(Ioo (h.rec a.2) b.2) else 0 :=
  card_sigmaLift (fun _ => Ioo) _ _

end

variable (i : ι) (a b : α i)
