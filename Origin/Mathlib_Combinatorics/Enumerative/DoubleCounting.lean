/-
Extracted from Combinatorics/Enumerative/DoubleCounting.lean
Genuine: 2 of 4 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Double counting

This file gathers a few double counting arguments.

## Bipartite graphs

In a bipartite graph (considered as a relation `r : α → β → Prop`), we can bound the number of edges
between `s : Finset α` and `t : Finset β` by the minimum/maximum of edges over all `a ∈ s` times the
size of `s`. Similarly for `t`. Combining those two yields inequalities between the sizes of `s`
and `t`.

* `bipartiteBelow`: `s.bipartiteBelow r b` are the elements of `s` below `b` w.r.t. `r`. Its size
  is the number of edges of `b` in `s`.
* `bipartiteAbove`: `t.bipartite_Above r a` are the elements of `t` above `a` w.r.t. `r`. Its size
  is the number of edges of `a` in `t`.
* `card_mul_le_card_mul`, `card_mul_le_card_mul'`: Double counting the edges of a bipartite graph
  from below and from above.
* `card_mul_eq_card_mul`: Equality combination of the previous.

## Implementation notes

For the formulation of double-counting arguments where a bipartite graph is considered as a
bipartite simple graph `G : SimpleGraph V`, see `Mathlib/Combinatorics/SimpleGraph/Bipartite.lean`.
-/

assert_not_exists Field

open Finset Function Relator

variable {R α β : Type*}

/-! ### Bipartite graph -/

namespace Finset

section Bipartite

variable (r : α → β → Prop) (s : Finset α) (t : Finset β) (a : α) (b : β)
  [DecidablePred (r a)] [∀ a, Decidable (r a b)] {m n : ℕ}

def bipartiteBelow : Finset α := {a ∈ s | r a b}

def bipartiteAbove : Finset β := {b ∈ t | r a b}
