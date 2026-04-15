/-
Extracted from Data/Finset/Density.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Density of a finite set

This defines the density of a `Finset` and provides induction principles for finsets.

## Main declarations

* `Finset.dens s`: Density of `s : Finset α` in `α` as a nonnegative rational number.

## Implementation notes

There are many other ways to talk about the density of a finset and provide its API:
1. Use the uniform measure
2. Define finitely additive functions and generalise the `Finset.card` API to it. This could either
  be done with
  a. A structure `FinitelyAdditiveFun`
  b. A typeclass `IsFinitelyAdditiveFun`

Solution 1 would mean importing measure theory in simple files (not necessarily bad, but not
amazing), and every single API lemma would require the user to prove that all the sets they are
talking about are measurable in the trivial sigma-algebra (quite terrible user experience).

Solution 2 would mean that some API lemmas about density don't contain `dens` in their name because
they are general results about finitely additive functions. But not all lemmas would be like that
either since some really are `dens`-specific. Hence the user would need to think about whether the
lemma they are looking for is generally true for finitely additive measure or whether it is
`dens`-specific.

On top of this, solution 2.a would break dot notation on `Finset.dens` (possibly fixable by
introducing notation for `⇑Finset.dens`) and solution 2.b would run the risk of being bad
performance-wise.

These considerations more generally apply to `Finset.card` and `Finset.sum` and demonstrate that
overengineering basic definitions is likely to hinder user experience.
-/

open Function Multiset Nat

variable {𝕜 α β : Type*} [Fintype α]

namespace Finset

variable {s t : Finset α} {a b : α}

def dens (s : Finset α) : ℚ≥0 := s.card / Fintype.card α
