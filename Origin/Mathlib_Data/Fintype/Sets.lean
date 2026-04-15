/-
Extracted from Data/Fintype/Sets.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Subsets of finite types

In a `Fintype`, all `Set`s are automatically `Finset`s, and there are only finitely many of them.

## Main results

* `Set.toFinset`: convert a subset of a finite type to a `Finset`
* `Finset.fintypeCoeSort`: `((s : Finset α) : Type*)` is a finite type
* `Fintype.finsetEquivSet`: `Finset α` and `Set α` are equivalent if `α` is a `Fintype`
-/

assert_not_exists Monoid

open Function

open Nat

universe u v

variable {α β γ : Type*}

open Finset

namespace Set

variable {s t : Set α}

def toFinset (s : Set α) [Fintype s] : Finset α :=
  (@Finset.univ s _).map <| Function.Embedding.subtype _
