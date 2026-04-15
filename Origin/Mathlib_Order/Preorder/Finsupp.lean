/-
Extracted from Order/Preorder/Finsupp.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Pointwise order on finitely supported functions

This file lifts order structures on `M` to `ι →₀ M`.
-/

assert_not_exists CompleteLattice

noncomputable section

open Finset

namespace Finsupp

variable {ι M : Type*} [Zero M]

section LE

variable [LE M] {f g : ι →₀ M}

-- INSTANCE (free from Core): instLE

lemma le_def : f ≤ g ↔ ∀ i, f i ≤ g i := .rfl
