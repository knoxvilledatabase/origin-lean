/-
Extracted from Logic/Equiv/Pairwise.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Interaction of equivalences with `Pairwise`
-/

open scoped Function -- required for scoped `on` notation

lemma EquivLike.pairwise_comp_iff {X : Type*} {Y : Type*} {F} [EquivLike F Y X]
    (f : F) (p : X → X → Prop) : Pairwise (p on f) ↔ Pairwise p :=
  (EquivLike.bijective f).pairwise_comp_iff
