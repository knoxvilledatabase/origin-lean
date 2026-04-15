/-
Extracted from Data/List/ChainOfFn.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Data.List.Chain
import Mathlib.Data.List.OfFn

/-!
# Lemmas about `Chain'` and `OfFn`

This file provides lemmas involving both `List.Chain'` and `List.OfFn`.
-/

open Nat

namespace List

lemma chain'_ofFn {α : Type*} {n : ℕ} {f : Fin n → α} {r : α → α → Prop} :
    (ofFn f).Chain' r ↔ ∀ (i) (hi : i + 1 < n), r (f ⟨i, lt_of_succ_lt hi⟩) (f ⟨i + 1, hi⟩) := by
  simp_rw [chain'_iff_get, get_ofFn, length_ofFn]
  exact ⟨fun h i hi ↦ h i (by omega), fun h i hi ↦ h i (by omega)⟩

end List
