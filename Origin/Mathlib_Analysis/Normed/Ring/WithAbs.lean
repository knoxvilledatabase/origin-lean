/-
Extracted from Analysis/Normed/Ring/WithAbs.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# `WithAbs` type synonym

`WithAbs v` is a copy of the semiring `R` with the same underlying ring structure, but assigned
`v`-dependent instances (such as `NormedRing`) where `v` is an absolute value on `R`.

## Main definitions
- `WithAbs` : type synonym for a semiring which depends on an absolute value. This is
  a function that takes an absolute value on a semiring and returns the semiring. This can be used
  to assign and infer instances on a semiring that depend on absolute values.
- `WithAbs.equiv v` : The canonical ring equivalence between `WithAbs v` and `R`.
-/

open Topology

variable {R : Type*} {S : Type*} [Semiring S] [PartialOrder S]

structure WithAbs [Semiring R] (v : AbsoluteValue R S) where
  /-- Converts an element of `R` to an element of `WithAbs v`. -/
  toAbs (v) ::
  /-- Converts an element of `WithAbs v` to an element of `R`. -/
  ofAbs : R

section Notation

open Lean.PrettyPrinter.Delaborator
