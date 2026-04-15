/-
Extracted from Data/NNReal/Defs.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Nonnegative real numbers

In this file we define `NNReal` (notation: `ℝ≥0`) to be the type of non-negative real numbers,
a.k.a. the interval `[0, ∞)`. We also define the following operations and structures on `ℝ≥0`:

* the order on `ℝ≥0` is the restriction of the order on `ℝ`; these relations define a conditionally
  complete linear order with a bottom element, `ConditionallyCompleteLinearOrderBot`;

* `a + b` and `a * b` are the restrictions of addition and multiplication of real numbers to `ℝ≥0`;
  these operations together with `0 = ⟨0, _⟩` and `1 = ⟨1, _⟩` turn `ℝ≥0` into a conditionally
  complete linear ordered archimedean commutative semifield; we have no typeclass for this in
  `mathlib` yet, so we define the following instances instead:

  - `LinearOrderedSemiring ℝ≥0`;
  - `OrderedCommSemiring ℝ≥0`;
  - `CanonicallyOrderedAdd ℝ≥0`;
  - `LinearOrderedCommGroupWithZero ℝ≥0`;
  - `CanonicallyLinearOrderedAddCommMonoid ℝ≥0`;
  - `Archimedean ℝ≥0`;
  - `ConditionallyCompleteLinearOrderBot ℝ≥0`.

  These instances are derived from corresponding instances about the type `{x : α // 0 ≤ x}` in an
  appropriate ordered field/ring/group/monoid `α`, see `Mathlib/Algebra/Order/Nonneg/Ring.lean`.

* `Real.toNNReal x` is defined as `⟨max x 0, _⟩`, i.e. `↑(Real.toNNReal x) = x` when `0 ≤ x` and
  `↑(Real.toNNReal x) = 0` otherwise.

We also define an instance `CanLift ℝ ℝ≥0`. This instance can be used by the `lift` tactic to
replace `x : ℝ` and `hx : 0 ≤ x` in the proof context with `x : ℝ≥0` while replacing all occurrences
of `x` with `↑x`. This tactic also works for a function `f : α → ℝ` with a hypothesis
`hf : ∀ x, 0 ≤ f x`.

## Notation

This file defines `ℝ≥0` as a localized notation for `NNReal`.
-/

assert_not_exists TrivialStar

open Function

def NNReal := { r : ℝ // 0 ≤ r }

namespace NNReal
