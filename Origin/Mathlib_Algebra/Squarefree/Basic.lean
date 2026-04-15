/-
Extracted from Algebra/Squarefree/Basic.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Squarefree elements of monoids
An element of a monoid is squarefree when it is not divisible by any squares
except the squares of units.

Results about squarefree natural numbers are proved in `Data.Nat.Squarefree`.

## Main Definitions
- `Squarefree r` indicates that `r` is only divisible by `x * x` if `x` is a unit.

## Main Results
- `multiplicity.squarefree_iff_emultiplicity_le_one`: `x` is `Squarefree` iff for every `y`, either
  `emultiplicity y x ≤ 1` or `IsUnit y`.
- `UniqueFactorizationMonoid.squarefree_iff_nodup_factors`: A nonzero element `x` of a unique
  factorization monoid is squarefree iff `factors x` has no duplicate factors.

## Tags
squarefree, multiplicity

-/

variable {R : Type*}

def Squarefree [Monoid R] (r : R) : Prop :=
  ∀ x : R, x * x ∣ r → IsUnit x

theorem IsRelPrime.of_squarefree_mul [CommMonoid R] {m n : R} (h : Squarefree (m * n)) :
    IsRelPrime m n := fun c hca hcb ↦ h c (mul_dvd_mul hca hcb)
