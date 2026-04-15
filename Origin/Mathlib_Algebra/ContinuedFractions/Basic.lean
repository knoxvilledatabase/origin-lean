/-
Extracted from Algebra/ContinuedFractions/Basic.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Basic Definitions/Theorems for Continued Fractions

## Summary

We define generalised, simple, and regular continued fractions and functions to evaluate their
convergents. We follow the naming conventions from Wikipedia and [wall2018analytic], Chapter 1.

## Main definitions

1. Generalised continued fractions (gcfs)
2. Simple continued fractions (scfs)
3. (Regular) continued fractions ((r)cfs)
4. Computation of convergents using the recurrence relation in `convs`.
5. Computation of convergents by directly evaluating the fraction described by the gcf in `convs'`.

## Implementation notes

1. The most commonly used kind of continued fractions in the literature are regular continued
   fractions. We hence just call them `ContFract` in the library.
2. We use sequences from `Data.Seq` to encode potentially infinite sequences.

## References

- <https://en.wikipedia.org/wiki/Generalized_continued_fraction>
- [Wall, H.S., *Analytic Theory of Continued Fractions*][wall2018analytic]

## Tags

numerics, number theory, approximations, fractions
-/

variable (α : Type*)

/-!### Definitions -/

structure GenContFract.Pair where
  /-- Partial numerator -/
  a : α
  /-- Partial denominator -/
  b : α
  deriving Inhabited

open GenContFract

/-! Interlude: define some expected coercions and instances. -/

namespace GenContFract.Pair

variable {α}

-- INSTANCE (free from Core): [Repr

def map {β : Type*} (f : α → β) (gp : Pair α) : Pair β :=
  ⟨f gp.a, f gp.b⟩

section coe

variable {β : Type*} [Coe α β]
