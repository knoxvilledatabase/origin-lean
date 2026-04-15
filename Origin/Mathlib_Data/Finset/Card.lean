/-
Extracted from Data/Finset/Card.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Cardinality of a finite set

This defines the cardinality of a `Finset` and provides induction principles for finsets.

## Main declarations

* `Finset.card`: `#s : ℕ` returns the cardinality of `s : Finset α`.

### Induction principles

* `Finset.strongInduction`: Strong induction
* `Finset.strongInductionOn`
* `Finset.strongDownwardInduction`
* `Finset.strongDownwardInductionOn`
* `Finset.case_strong_induction_on`
* `Finset.Nonempty.strong_induction`
* `Finset.eraseInduction`
-/

assert_not_exists Monoid

open Function Multiset Nat

variable {α β R : Type*}

namespace Finset

variable {s t : Finset α} {a b : α}

def card (s : Finset α) : ℕ :=
  Multiset.card s.1
