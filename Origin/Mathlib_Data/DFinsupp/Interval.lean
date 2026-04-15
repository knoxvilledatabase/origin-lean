/-
Extracted from Data/DFinsupp/Interval.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Finite intervals of finitely supported functions

This file provides the `LocallyFiniteOrder` instance for `Π₀ i, α i` when `α` itself is locally
finite and calculates the cardinality of its finite intervals.
-/

open DFinsupp Finset

open Pointwise

variable {ι : Type*} {α : ι → Type*}

namespace Finset

variable [DecidableEq ι] [∀ i, Zero (α i)] {s : Finset ι} {f : Π₀ i, α i} {t : ∀ i, Finset (α i)}

def dfinsupp (s : Finset ι) (t : ∀ i, Finset (α i)) : Finset (Π₀ i, α i) :=
  (s.pi t).map
    ⟨fun f => DFinsupp.mk s fun i => f i i.2, by
      refine (mk_injective _).comp fun f g h => ?_
      ext i hi
      convert congr_fun h ⟨i, hi⟩⟩
