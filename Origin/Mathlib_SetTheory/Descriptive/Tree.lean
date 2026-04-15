/-
Extracted from SetTheory/Descriptive/Tree.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Trees in the sense of descriptive set theory

This file defines trees of depth `ω` in the sense of descriptive set theory as sets of finite
sequences that are stable under taking prefixes.

## Main declarations

* `tree A`: a (possibly infinite) tree of depth at most `ω` with nodes in `A`
-/

namespace Descriptive

def tree (A : Type*) : CompleteSublattice (Set (List A)) :=
  CompleteSublattice.mk' {T | ∀ ⦃x : List A⦄ ⦃a : A⦄, x ++ [a] ∈ T → x ∈ T}
    (by rintro S hS x a ⟨t, ht, hx⟩; use t, ht, hS ht hx)
    (by rintro S hS x a h T hT; exact hS hT <| h T hT)
