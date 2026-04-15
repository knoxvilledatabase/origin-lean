/-
Extracted from Data/NNRat/Defs.lean
Genuine: 4 of 12 | Dissolved: 0 | Infrastructure: 8
-/
import Origin.Core

/-!
# Nonnegative rationals

This file defines the nonnegative rationals as a subtype of `Rat` and provides its basic algebraic
order structure.

Note that `NNRat` is not declared as a `Semifield` here. See `Mathlib/Algebra/Field/Rat.lean` for
that instance.

We also define an instance `CanLift ℚ ℚ≥0`. This instance can be used by the `lift` tactic to
replace `x : ℚ` and `hx : 0 ≤ x` in the proof context with `x : ℚ≥0` while replacing all occurrences
of `x` with `↑x`. This tactic also works for a function `f : α → ℚ` with a hypothesis
`hf : ∀ x, 0 ≤ f x`.

## Notation

`ℚ≥0` is notation for `NNRat` in scope `NNRat`.

## Huge warning

Whenever you state a lemma about the coercion `ℚ≥0 → ℚ`, check that Lean inserts `NNRat.cast`, not
`Subtype.val`. Else your lemma will never apply.
-/

assert_not_exists CompleteLattice IsOrderedMonoid

library_note «specialised high priority simp lemma» /--

It sometimes happens that a `@[simp]` lemma declared early in the library can be proved by `simp`

using later, more general simp lemmas. In that case, the following reasons might be arguments for

the early lemma to be tagged `@[simp high]` (rather than `@[simp, nolint simpNF]` or

un-`@[simp]`ed):

1. There is a significant portion of the library which needs the early lemma to be available via
  `simp` and which doesn't have access to the more general lemmas.

2. The more general lemmas have more complicated typeclass assumptions, causing rewrites with them
  to be slower.

-/

open Function

-- INSTANCE (free from Core): Rat.instPosMulMono

-- INSTANCE (free from Core): CommSemiring

-- INSTANCE (free from Core): AddCancelCommMonoid

-- INSTANCE (free from Core): LinearOrder

-- INSTANCE (free from Core): Sub

-- INSTANCE (free from Core): Inhabited

namespace NNRat

variable {p q : ℚ≥0}

-- INSTANCE (free from Core): instNontrivial

-- INSTANCE (free from Core): instOrderBot
