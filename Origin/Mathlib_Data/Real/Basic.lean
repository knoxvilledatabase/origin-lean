/-
Extracted from Data/Real/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Real numbers from Cauchy sequences

This file defines `ℝ` as the type of equivalence classes of Cauchy sequences of rational numbers.
This choice is motivated by how easy it is to prove that `ℝ` is a commutative ring, by simply
lifting everything to `ℚ`.

The facts that the real numbers are an Archimedean floor ring,
and a conditionally complete linear order,
have been deferred to the file `Mathlib/Data/Real/Archimedean.lean`,
in order to keep the imports here simple.

The fact that the real numbers are a (trivial) *-ring has similarly been deferred to
`Mathlib/Data/Real/Star.lean`.
-/

assert_not_exists Finset Module Submonoid FloorRing

structure Real where ofCauchy ::
  /-- The underlying Cauchy completion -/
  cauchy : CauSeq.Completion.Cauchy (abs : ℚ → ℚ)
