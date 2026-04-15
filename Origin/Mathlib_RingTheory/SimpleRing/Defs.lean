/-
Extracted from RingTheory/SimpleRing/Defs.lean
Genuine: 1 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.RingTheory.TwoSidedIdeal.Lattice
import Mathlib.Order.Atoms

/-! # Simple rings

A ring `R` is **simple** if it has only two two-sided ideals, namely `⊥` and `⊤`.

## Main definitions

- `IsSimpleRing`: a predicate expressing that a ring is simple.

-/

class IsSimpleRing (R : Type*) [NonUnitalNonAssocRing R] : Prop where
  simple : IsSimpleOrder (TwoSidedIdeal R)
