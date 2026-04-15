/-
Extracted from Data/DFinsupp/Multiset.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Equivalence between `Multiset` and `ℕ`-valued finitely supported functions

This defines `DFinsupp.toMultiset` the equivalence between `Π₀ a : α, ℕ` and `Multiset α`, along
with `Multiset.toDFinsupp` the reverse equivalence.
-/

open Function

variable {α : Type*}

namespace DFinsupp

-- INSTANCE (free from Core): addZeroClass'

variable [DecidableEq α]

def toMultiset : (Π₀ _ : α, ℕ) →+ Multiset α :=
  DFinsupp.sumAddHom fun a : α ↦ Multiset.replicateAddMonoidHom a
