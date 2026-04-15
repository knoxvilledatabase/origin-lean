/-
Extracted from Data/Multiset/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Basic results on multisets

-/

assert_not_exists Monoid

universe v

open List Subtype Nat Function

variable {α : Type*} {β : Type v} {γ : Type*}

namespace Multiset

/-! ### `Multiset.toList` -/

section ToList

noncomputable def toList (s : Multiset α) :=
  s.out
