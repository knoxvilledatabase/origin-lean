/-
Extracted from Algebra/EuclideanDomain/Defs.lean
Genuine: 4 of 11 | Dissolved: 3 | Infrastructure: 4
-/
import Origin.Core

/-!
# Euclidean domains

This file introduces Euclidean domains and provides the extended Euclidean algorithm. To be precise,
a slightly more general version is provided which is sometimes called a transfinite Euclidean domain
and differs in the fact that the degree function need not take values in `ℕ` but can take values in
any well-ordered set. Transfinite Euclidean domains were introduced by Motzkin and examples which
don't satisfy the classical notion were provided independently by Hiblot and Nagata.

## Main definitions

* `EuclideanDomain`: Defines Euclidean domain with functions `quotient` and `remainder`. Instances
  of `Div` and `Mod` are provided, so that one can write `a = b * (a / b) + a % b`.
* `gcd`: defines the greatest common divisors of two elements of a Euclidean domain.
* `xgcd`: given two elements `a b : R`, `xgcd a b` defines the pair `(x, y)` such that
  `x * a + y * b = gcd a b`.
* `lcm`: defines the lowest common multiple of two elements `a` and `b` of a Euclidean domain as
  `a * b / (gcd a b)`

## Main statements

See `Algebra.EuclideanDomain.Basic` for most of the theorems about Euclidean domains,
including Bézout's lemma.

See `Algebra.EuclideanDomain.Instances` for the fact that `ℤ` is a Euclidean domain,
as is any field.

## Notation

`≺` denotes the well-founded relation on the Euclidean domain, e.g. in the example of the polynomial
ring over a field, `p ≺ q` for polynomials `p` and `q` if and only if the degree of `p` is less than
the degree of `q`.

## Implementation details

Instead of working with a valuation, `EuclideanDomain` is implemented with the existence of a well
founded relation `r` on the integral domain `R`, which in the example of `ℤ` would correspond to
setting `i ≺ j` for integers `i` and `j` if the absolute value of `i` is smaller than the absolute
value of `j`.

## References

* [Th. Motzkin, *The Euclidean algorithm*][MR32592]
* [J.-J. Hiblot, *Des anneaux euclidiens dont le plus petit algorithme n'est pas à valeurs finies*]
  [MR399081]
* [M. Nagata, *On Euclid algorithm*][MR541021]


## Tags

Euclidean domain, transfinite Euclidean domain, Bézout's lemma
-/

universe u

-- DISSOLVED: EuclideanDomain

namespace EuclideanDomain

variable {R : Type u} [EuclideanDomain R]

local infixl:50 " ≺ " => EuclideanDomain.r

-- INSTANCE (free from Core): wellFoundedRelation

-- INSTANCE (free from Core): isWellFounded

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

theorem div_add_mod (a b : R) : b * (a / b) + a % b = a :=
  EuclideanDomain.quotient_mul_add_remainder_eq _ _

theorem mod_add_div (a b : R) : a % b + b * (a / b) = a :=
  (add_comm _ _).trans (div_add_mod _ _)

theorem mod_add_div' (m k : R) : m % k + m / k * k = m := by
  rw [mul_comm]
  exact mod_add_div _ _

theorem div_add_mod' (m k : R) : m / k * k + m % k = m := by
  rw [mul_comm]
  exact div_add_mod _ _

-- DISSOLVED: mod_lt

-- DISSOLVED: mul_right_not_lt
