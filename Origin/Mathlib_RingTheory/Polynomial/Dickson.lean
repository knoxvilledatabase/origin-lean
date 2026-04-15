/-
Extracted from RingTheory/Polynomial/Dickson.lean
Genuine: 8 | Conflates: 0 | Dissolved: 7 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.Algebra.CharP.Invertible
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Polynomial.Roots

/-!
# Dickson polynomials

The (generalised) Dickson polynomials are a family of polynomials indexed by `ℕ × ℕ`,
with coefficients in a commutative ring `R` depending on an element `a∈R`. More precisely, the
they satisfy the recursion `dickson k a (n + 2) = X * (dickson k a n + 1) - a * (dickson k a n)`
with starting values `dickson k a 0 = 3 - k` and `dickson k a 1 = X`. In the literature,
`dickson k a n` is called the `n`-th Dickson polynomial of the `k`-th kind associated to the
parameter `a : R`. They are closely related to the Chebyshev polynomials in the case that `a=1`.
When `a=0` they are just the family of monomials `X ^ n`.

## Main definition

* `Polynomial.dickson`: the generalised Dickson polynomials.

## Main statements

* `Polynomial.dickson_one_one_mul`, the `(m * n)`-th Dickson polynomial of the first kind for
  parameter `1 : R` is the composition of the `m`-th and `n`-th Dickson polynomials of the first
  kind for `1 : R`.
* `Polynomial.dickson_one_one_charP`, for a prime number `p`, the `p`-th Dickson polynomial of the
  first kind associated to parameter `1 : R` is congruent to `X ^ p` modulo `p`.

## References

* [R. Lidl, G. L. Mullen and G. Turnwald, _Dickson polynomials_][MR1237403]

## TODO

* Redefine `dickson` in terms of `LinearRecurrence`.
* Show that `dickson 2 1` is equal to the characteristic polynomial of the adjacency matrix of a
  type A Dynkin diagram.
* Prove that the adjacency matrices of simply laced Dynkin diagrams are precisely the adjacency
  matrices of simple connected graphs which annihilate `dickson 2 1`.
-/

noncomputable section

namespace Polynomial

variable {R S : Type*} [CommRing R] [CommRing S] (k : ℕ) (a : R)

noncomputable def dickson : ℕ → R[X]
  | 0 => 3 - k
  | 1 => X
  | n + 2 => X * dickson (n + 1) - C a * dickson n

@[simp]
theorem dickson_zero : dickson k a 0 = 3 - k :=
  rfl

@[simp]
theorem dickson_one : dickson k a 1 = X :=
  rfl

theorem dickson_two : dickson k a 2 = X ^ 2 - C a * (3 - k : R[X]) := by
  simp only [dickson, sq]

@[simp]
theorem dickson_add_two (n : ℕ) :
    dickson k a (n + 2) = X * dickson k a (n + 1) - C a * dickson k a n := by rw [dickson]

theorem dickson_of_two_le {n : ℕ} (h : 2 ≤ n) :
    dickson k a n = X * dickson k a (n - 1) - C a * dickson k a (n - 2) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [add_comm]
  exact dickson_add_two k a n

variable {k a}

theorem map_dickson (f : R →+* S) : ∀ n : ℕ, map f (dickson k a n) = dickson k (f a) n
  | 0 => by
    simp_rw [dickson_zero, Polynomial.map_sub, Polynomial.map_natCast, Polynomial.map_ofNat]
  | 1 => by simp only [dickson_one, map_X]
  | n + 2 => by
    simp only [dickson_add_two, Polynomial.map_sub, Polynomial.map_mul, map_X, map_C]
    rw [map_dickson f n, map_dickson f (n + 1)]

@[simp]
theorem dickson_two_zero : ∀ n : ℕ, dickson 2 (0 : R) n = X ^ n
  | 0 => by
    simp only [dickson_zero, pow_zero]
    norm_num
  | 1 => by simp only [dickson_one, pow_one]
  | n + 2 => by
    simp only [dickson_add_two, C_0, zero_mul, sub_zero]
    rw [dickson_two_zero (n + 1), pow_add X (n + 1) 1, mul_comm, pow_one]

section Dickson

/-!

### A Lambda structure on `ℤ[X]`

Mathlib doesn't currently know what a Lambda ring is.
But once it does, we can endow `ℤ[X]` with a Lambda structure
in terms of the `dickson 1 1` polynomials defined below.
There is exactly one other Lambda structure on `ℤ[X]` in terms of binomial polynomials.

-/

-- DISSOLVED: dickson_one_one_eval_add_inv

variable (R)

private theorem two_mul_C_half_eq_one [Invertible (2 : R)] : 2 * C (⅟ 2 : R) = 1 := by
  rw [two_mul, ← C_add, invOf_two_add_invOf_two, C_1]

private theorem C_half_mul_two_eq_one [Invertible (2 : R)] : C (⅟ 2 : R) * 2 = 1 := by
  rw [mul_comm, two_mul_C_half_eq_one]

-- DISSOLVED: dickson_one_one_eq_chebyshev_T

-- DISSOLVED: chebyshev_T_eq_dickson_one_one

-- DISSOLVED: dickson_one_one_mul

-- DISSOLVED: dickson_one_one_comp_comm

-- DISSOLVED: dickson_one_one_zmod_p

-- DISSOLVED: dickson_one_one_charP

end Dickson

end Polynomial
