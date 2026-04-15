/-
Extracted from Order/Preorder/Chain.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Chains and flags

This file defines chains for an arbitrary relation and flags for an order.

## Main declarations

* `IsChain s`: A chain `s` is a set of comparable elements.
* `Flag`: The type of flags, aka maximal chains, of an order.

## Notes

Originally ported from Isabelle/HOL. The
[original file](https://isabelle.in.tum.de/dist/library/HOL/HOL/Zorn.html) was written by Jacques D.
Fleuriot, Tobias Nipkow, Christian Sternagel.
-/

assert_not_exists CompleteLattice

open Set Set.Notation

variable {α β F : Type*}

/-! ### Chains -/

section Chain

variable (r : α → α → Prop)

local infixl:50 " ≺ " => r

def IsChain (s : Set α) : Prop :=
  s.Pairwise fun x y => x ≺ y ∨ y ≺ x

def SuperChain (s t : Set α) : Prop :=
  IsChain r t ∧ s ⊂ t

def IsMaxChain (s : Set α) : Prop :=
  IsChain r s ∧ ∀ ⦃t⦄, IsChain r t → s ⊆ t → s = t

variable {r} {c c₁ c₂ s t : Set α} {a b x y : α}
