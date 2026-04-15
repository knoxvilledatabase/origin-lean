/-
Extracted from Data/Finset/Fold.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The fold operation for a commutative associative operation over a finset.
-/

assert_not_exists Monoid

namespace Finset

open Multiset

variable {α β γ : Type*}

/-! ### fold -/

section Fold

variable (op : β → β → β) [hc : Std.Commutative op] [ha : Std.Associative op]

local notation a " * " b => op a b

def fold (b : β) (f : α → β) (s : Finset α) : β :=
  (s.1.map f).fold op b

variable {op} {f : α → β} {b : β} {s : Finset α} {a : α}
