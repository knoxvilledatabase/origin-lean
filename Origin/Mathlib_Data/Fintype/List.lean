/-
Extracted from Data/Fintype/List.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Fintype instance for nodup lists

The subtype of `{l : List α // l.Nodup}` over a `[Fintype α]`
admits a `Fintype` instance.

## Implementation details
To construct the `Fintype` instance, a function lifting a `Multiset α`
to the `Multiset (List α)` is provided.
This function is applied to the `Finset.powerset` of `Finset.univ`.

-/

variable {α : Type*}

open List

namespace Multiset

def lists : Multiset α → Multiset (List α) := fun s =>
  Quotient.liftOn s (fun l => l.permutations) fun l l' (h : l ~ l') => by
    simp only
    refine coe_eq_coe.mpr ?_
    exact Perm.permutations h
