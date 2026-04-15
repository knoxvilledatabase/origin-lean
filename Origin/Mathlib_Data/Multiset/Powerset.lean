/-
Extracted from Data/Multiset/Powerset.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# The powerset of a multiset
-/

namespace Multiset

open List

variable {α : Type*}

/-! ### powerset -/

def powersetAux (l : List α) : List (Multiset α) :=
  (sublists l).map (↑)
