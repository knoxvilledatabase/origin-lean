/-
Extracted from Algebra/Ring/NegOnePow.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Integer powers of (-1)

This file defines the map `negOnePow : ℤ → ℤˣ` which sends `n` to `(-1 : ℤˣ) ^ n`.

The definition of `negOnePow` and some lemmas first appeared in contributions by
Johan Commelin to the Liquid Tensor Experiment.

-/

assert_not_exists Field

assert_not_exists TwoSidedIdeal

namespace Int

def negOnePow (n : ℤ) : ℤˣ := (-1 : ℤˣ) ^ n

lemma negOnePow_add (n₁ n₂ : ℤ) :
    (n₁ + n₂).negOnePow = n₁.negOnePow * n₂.negOnePow :=
  zpow_add _ _ _
