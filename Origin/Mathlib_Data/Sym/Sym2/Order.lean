/-
Extracted from Data/Sym/Sym2/Order.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Sorting the elements of `Sym2`

This file provides `Sym2.sortEquiv`, the forward direction of which is somewhat analogous to
`Multiset.sort`.
-/

namespace Sym2

variable {α}

def sup [SemilatticeSup α] (x : Sym2 α) : α := Sym2.lift ⟨(· ⊔ ·), sup_comm⟩ x
