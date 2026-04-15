/-
Extracted from RingTheory/WittVector/FrobeniusFractionField.lean
Genuine: 4 of 17 | Dissolved: 13 | Infrastructure: 0
-/
import Origin.Core

/-!
# Solving equations about the Frobenius map on the field of fractions of `𝕎 k`

The goal of this file is to prove `WittVector.exists_frobenius_solution_fractionRing`,
which says that for an algebraically closed field `k` of characteristic `p` and `a, b` in the
field of fractions of Witt vectors over `k`,
there is a solution `b` to the equation `φ b * a = p ^ m * b`, where `φ` is the Frobenius map.

Most of this file builds up the equivalent theorem over `𝕎 k` directly,
moving to the field of fractions at the end.
See `WittVector.frobeniusRotation` and its specification.

The construction proceeds by recursively defining a sequence of coefficients as solutions to a
polynomial equation in `k`. We must define these as generic polynomials using Witt vector API
(`WittVector.wittMul`, `wittPolynomial`) to show that they satisfy the desired equation.

Preliminary work is done in the dependency `RingTheory.WittVector.MulCoeff`
to isolate the `n+1`st coefficients of `x` and `y` in the `n+1`st coefficient of `x*y`.

This construction is described in Dupuis, Lewis, and Macbeth,
[Formalized functional analysis via semilinear maps][dupuis-lewis-macbeth2022].
We approximately follow an approach sketched on MathOverflow:
<https://mathoverflow.net/questions/62468/about-frobenius-of-witt-vectors>

The result is a dependency for the proof of `WittVector.isocrystal_classification`,
the classification of one-dimensional isocrystals over an algebraically closed field.
-/

noncomputable section

namespace WittVector

variable (p : ℕ) [hp : Fact p.Prime]

local notation "𝕎" => WittVector p

namespace RecursionMain

/-!

## The recursive case of the vector coefficients

The first coefficient of our solution vector is easy to define below.
In this section we focus on the recursive case.
The goal is to turn `WittVector.wittPolyProd n` into a univariate polynomial
whose variable represents the `n`th coefficient of `x` in `x * a`.

-/

section CommRing

variable {k : Type*} [CommRing k] [CharP k p]

open Polynomial

def succNthDefiningPoly (n : ℕ) (a₁ a₂ : 𝕎 k) (bs : Fin (n + 1) → k) : Polynomial k :=
  X ^ p * C (a₁.coeff 0 ^ p ^ (n + 1)) - X * C (a₂.coeff 0 ^ p ^ (n + 1)) +
    C
      (a₁.coeff (n + 1) * (bs 0 ^ p) ^ p ^ (n + 1) +
            nthRemainder p n (fun v => bs v ^ p) (truncateFun (n + 1) a₁) -
          a₂.coeff (n + 1) * bs 0 ^ p ^ (n + 1) -
        nthRemainder p n bs (truncateFun (n + 1) a₂))

-- DISSOLVED: succNthDefiningPoly_degree

end CommRing

section IsAlgClosed

variable {k : Type*} [Field k] [CharP k p] [IsAlgClosed k]

-- DISSOLVED: root_exists

-- DISSOLVED: succNthVal

-- DISSOLVED: succNthVal_spec

-- DISSOLVED: succNthVal_spec'

end IsAlgClosed

end RecursionMain

namespace RecursionBase

variable {k : Type*} [Field k] [IsAlgClosed k]

theorem solution_pow (a₁ a₂ : 𝕎 k) : ∃ x : k, x ^ (p - 1) = a₂.coeff 0 / a₁.coeff 0 :=
  IsAlgClosed.exists_pow_nat_eq _ <| tsub_pos_of_lt hp.out.one_lt

def solution (a₁ a₂ : 𝕎 k) : k :=
  Classical.choose <| solution_pow p a₁ a₂

theorem solution_spec (a₁ a₂ : 𝕎 k) : solution p a₁ a₂ ^ (p - 1) = a₂.coeff 0 / a₁.coeff 0 :=
  Classical.choose_spec <| solution_pow p a₁ a₂

-- DISSOLVED: solution_nonzero

-- DISSOLVED: solution_spec'

end RecursionBase

open RecursionMain RecursionBase

section FrobeniusRotation

section IsAlgClosed

variable {k : Type*} [Field k] [CharP k p] [IsAlgClosed k]

-- DISSOLVED: frobeniusRotationCoeff

-- DISSOLVED: frobeniusRotation

-- DISSOLVED: frobeniusRotation_nonzero

-- DISSOLVED: frobenius_frobeniusRotation

local notation "φ" => IsFractionRing.ringEquivOfRingEquiv (frobeniusEquiv p k)

set_option linter.flexible false in

set_option linter.unusedSimpArgs false in

-- DISSOLVED: exists_frobenius_solution_fractionRing_aux

-- DISSOLVED: exists_frobenius_solution_fractionRing

end IsAlgClosed

end FrobeniusRotation

end WittVector
