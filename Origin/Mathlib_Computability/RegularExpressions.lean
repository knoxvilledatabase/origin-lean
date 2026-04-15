/-
Extracted from Computability/RegularExpressions.lean
Genuine: 1 of 7 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core

/-!
# Regular Expressions

This file contains the formal definition for regular expressions and basic lemmas. Note these are
regular expressions in terms of formal language theory. Note this is different to regexes used in
computer science such as the POSIX standard.

## TODO

Currently, we do not show that regular expressions and DFAs/NFAs are equivalent.
Multiple competing PRs towards that goal are in review.
See https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Regular.20languages.3A.20the.20review.20queue
-/

open List Set

open Computability

universe u

variable {α β γ : Type*}

set_option genSizeOfSpec false in

set_option genInjectivity false in

inductive RegularExpression (α : Type u) : Type u
  | zero : RegularExpression α
  | epsilon : RegularExpression α
  | char : α → RegularExpression α
  | plus : RegularExpression α → RegularExpression α → RegularExpression α
  | comp : RegularExpression α → RegularExpression α → RegularExpression α
  | star : RegularExpression α → RegularExpression α

namespace RegularExpression

variable {a b : α}

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :
