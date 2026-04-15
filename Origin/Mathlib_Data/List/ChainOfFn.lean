/-
Extracted from Data/List/ChainOfFn.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Lemmas about `IsChain` and `ofFn`

This file provides lemmas involving both `List.IsChain` and `List.ofFn`.
-/

open Nat

namespace List

lemma isChain_ofFn {α : Type*} {n : ℕ} {f : Fin n → α} {r : α → α → Prop} :
    (ofFn f).IsChain r ↔ ∀ (i) (hi : i + 1 < n), r (f ⟨i, lt_of_succ_lt hi⟩) (f ⟨i + 1, hi⟩) := by
  simp_rw [isChain_iff_getElem, List.getElem_ofFn, length_ofFn]

end List
