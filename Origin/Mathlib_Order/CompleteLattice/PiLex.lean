/-
Extracted from Order/CompleteLattice/PiLex.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Complete linear order instance on lexicographically ordered pi types

We show that for `α` a family of complete linear orders, the lexicographically ordered type of
dependent functions `Πₗ i, α i` is itself a complete linear order.
-/

variable {ι : Type*} {α : ι → Type*} [LinearOrder ι] [∀ i, CompleteLinearOrder (α i)]

namespace Pi

/-! ### Lexicographic ordering -/

namespace Lex

variable [WellFoundedLT ι]

private def inf [WellFoundedLT ι] (s : Set (Πₗ i, α i)) (i : ι) : α i :=
  ⨅ e : {e ∈ s | ∀ j < i, e j = inf s j}, e.1 i

termination_by wellFounded_lt.wrap i
