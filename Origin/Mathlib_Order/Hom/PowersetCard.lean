/-
Extracted from Order/Hom/PowersetCard.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Finite sets of an ordered type

This file defines the isomorphism between ordered embeddings into a linearly ordered type and
the finite sets of that type.

## Definitions

* `ofFinEmbEquiv` is the equivalence between `Fin n ↪o I` and `Set.powersetCard I n` when `I` is
  a linearly ordered type.

-/

open Finset Function Set

namespace Set.powersetCard

section order

variable {n : ℕ} {I : Type*} [LinearOrder I]

def ofFinEmbEquiv : (Fin n ↪o I) ≃ powersetCard I n where
  toFun f := ofFinEmb n I f.toEmbedding
  invFun s := Finset.orderEmbOfFin s.val s.prop
  left_inv f := by symm; apply Finset.orderEmbOfFin_unique'; simp
  right_inv s := by ext; simp
