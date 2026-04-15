/-
Extracted from Algebra/Order/Antidiag/Prod.lean
Genuine: 3 of 4 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-! # Antidiagonal with values in general types

We define a type class `Finset.HasAntidiagonal A` which contains a function
`antidiagonal : A → Finset (A × A)` such that `antidiagonal n`
is the finset of all pairs adding to `n`, as witnessed by `mem_antidiagonal`.

When `A` is a canonically ordered additive monoid with locally finite order
this typeclass can be instantiated with `Finset.antidiagonalOfLocallyFinite`.
This applies in particular when `A` is `ℕ`, more generally or `σ →₀ ℕ`,
or even `ι →₀ A`  under the additional assumption `OrderedSub A`
that make it a canonically ordered additive monoid.
(In fact, we would just need an `AddMonoid` with a compatible order,
finite `Iic`, such that if `a + b = n`, then `a, b ≤ n`,
and any finiteness condition would be OK.)

For computational reasons it is better to manually provide instances for `ℕ`
and `σ →₀ ℕ`, to avoid quadratic runtime performance.
These instances are provided as `Finset.Nat.instHasAntidiagonal` and `Finsupp.instHasAntidiagonal`.
This is why `Finset.antidiagonalOfLocallyFinite` is an `abbrev` and not an `instance`.

This definition does not exactly match with that of `Multiset.antidiagonal`
defined in `Mathlib/Data/Multiset/Antidiagonal.lean`, because of the multiplicities.
Indeed, by counting multiplicities, `Multiset α` is equivalent to `α →₀ ℕ`,
but `Finset.antidiagonal` and `Multiset.antidiagonal` will return different objects.
For example, for `s : Multiset ℕ := {0,0,0}`, `Multiset.antidiagonal s` has 8 elements
but `Finset.antidiagonal s` has only 4.

```lean
def s : Multiset ℕ := {0, 0, 0}
#eval (Finset.antidiagonal s).card -- 4
#eval Multiset.card (Multiset.antidiagonal s) -- 8
```

## TODO

* Define `HasMulAntidiagonal` (for monoids).
  For `PNat`, we will recover the set of divisors of a strictly positive integer.
-/

open Function

namespace Finset

class HasAntidiagonal (A : Type*) [AddMonoid A] where
  /-- The antidiagonal of an element `n` is the finset of pairs `(i, j)` such that `i + j = n`. -/
  antidiagonal : A → Finset (A × A)
  /-- A pair belongs to `antidiagonal n` iff the sum of its components is equal to `n`. -/
  mem_antidiagonal {n} {a} : a ∈ antidiagonal n ↔ a.fst + a.snd = n

export HasAntidiagonal (antidiagonal mem_antidiagonal)

attribute [simp] mem_antidiagonal

variable {A : Type*}

-- INSTANCE (free from Core): [AddMonoid

lemma hasAntidiagonal_congr (A : Type*) [AddMonoid A]
    [H1 : HasAntidiagonal A] [H2 : HasAntidiagonal A] :
    H1.antidiagonal = H2.antidiagonal := by congr!; subsingleton

theorem swap_mem_antidiagonal [AddCommMonoid A] [HasAntidiagonal A] {n : A} {xy : A × A} :
    xy.swap ∈ antidiagonal n ↔ xy ∈ antidiagonal n := by
  simp [add_comm]
