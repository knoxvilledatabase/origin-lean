/-
Extracted from Data/Finset/Option.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Finite sets in `Option α`

In this file we define

* `Option.toFinset`: construct an empty or singleton `Finset α` from an `Option α`;
* `Finset.insertNone`: given `s : Finset α`, lift it to a finset on `Option α` using `Option.some`
  and then insert `Option.none`;
* `Finset.eraseNone`: given `s : Finset (Option α)`, returns `t : Finset α` such that
  `x ∈ t ↔ some x ∈ s`.

Then we prove some basic lemmas about these definitions.

## Tags

finset, option
-/

variable {α β : Type*}

open Function

namespace Option

def toFinset (o : Option α) : Finset α :=
  o.elim ∅ singleton
