/-
Extracted from Data/Multiset/Fold.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# The fold operation for a commutative associative operation over a multiset.
-/

namespace Multiset

variable {α β : Type*}

/-! ### fold -/

section Fold

variable (op : α → α → α) [hc : Std.Commutative op] [ha : Std.Associative op]

local notation a " * " b => op a b

def fold : α → Multiset α → α :=
  foldr op
