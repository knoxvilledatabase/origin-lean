/-
Extracted from Data/Multiset/Replicate.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Repeating elements in multisets

## Main definitions

* `replicate n a` is the multiset containing only `a` with multiplicity `n`

-/

assert_not_exists Monoid

universe v

open List Subtype Nat Function

variable {α : Type*} {β : Type v} {γ : Type*}

namespace Multiset

/-! ### `Multiset.replicate` -/

def replicate (n : ℕ) (a : α) : Multiset α :=
  List.replicate n a
