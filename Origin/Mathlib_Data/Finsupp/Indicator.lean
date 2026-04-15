/-
Extracted from Data/Finsupp/Indicator.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Building finitely supported functions off finsets

This file defines `Finsupp.indicator` to help create finsupps from finsets.

## Main declarations

* `Finsupp.indicator`: Turns a map from a `Finset` into a `Finsupp` from the entire type.
-/

noncomputable section

open Finset Function

variable {ι α : Type*}

namespace Finsupp

variable [Zero α] {s t : Finset ι} (f : ∀ i ∈ s, α) {i : ι}

def indicator (s : Finset ι) (f : ∀ i ∈ s, α) : ι →₀ α where
  toFun i :=
    haveI := Classical.decEq ι
    if H : i ∈ s then f i H else 0
  support :=
    haveI := Classical.decEq α
    ({i | f i.1 i.2 ≠ 0} : Finset s).map (Embedding.subtype _)
  mem_support_toFun i := by
    classical simp

theorem indicator_of_mem (hi : i ∈ s) (f : ∀ i ∈ s, α) : indicator s f i = f i hi :=
  @dif_pos _ (id _) hi _ _ _

theorem indicator_of_notMem (hi : i ∉ s) (f : ∀ i ∈ s, α) : indicator s f i = 0 :=
  @dif_neg _ (id _) hi _ _ _

variable (s i)
