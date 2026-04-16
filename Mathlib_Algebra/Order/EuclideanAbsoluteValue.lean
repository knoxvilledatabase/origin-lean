/-
Extracted from Algebra/Order/EuclideanAbsoluteValue.lean
Genuine: 3 | Conflates: 0 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core
import Mathlib.Algebra.Order.AbsoluteValue
import Mathlib.Algebra.EuclideanDomain.Int

noncomputable section

/-!
# Euclidean absolute values

This file defines a predicate `AbsoluteValue.IsEuclidean abv` stating the
absolute value is compatible with the Euclidean domain structure on its domain.

## Main definitions

 * `AbsoluteValue.IsEuclidean abv` is a predicate on absolute values on `R` mapping to `S`
    that preserve the order on `R` arising from the Euclidean domain structure.
 * `AbsoluteValue.abs_isEuclidean` shows the "standard" absolute value on `ℤ`,
   mapping negative `x` to `-x`, is euclidean.
-/

local infixl:50 " ≺ " => EuclideanDomain.r

namespace AbsoluteValue

section OrderedSemiring

variable {R S : Type*} [EuclideanDomain R] [OrderedSemiring S]

variable (abv : AbsoluteValue R S)

structure IsEuclidean : Prop where
  /-- The requirement of a Euclidean absolute value
  that `abv` is monotone with respect to `≺` -/
  map_lt_map_iff' : ∀ {x y}, abv x < abv y ↔ x ≺ y

namespace IsEuclidean

variable {abv}

theorem map_lt_map_iff {x y : R} (h : abv.IsEuclidean) : abv x < abv y ↔ x ≺ y :=
  map_lt_map_iff' h

attribute [simp] map_lt_map_iff

theorem sub_mod_lt (h : abv.IsEuclidean) (a : R) {b : R} (hb : b ≠ 0) : abv (a % b) < abv b :=
  h.map_lt_map_iff.mpr (EuclideanDomain.mod_lt a hb)

end IsEuclidean

end OrderedSemiring

section Int

open Int

protected theorem abs_isEuclidean : IsEuclidean (AbsoluteValue.abs : AbsoluteValue ℤ ℤ) :=
  {  map_lt_map_iff' := fun {x y} =>
       show abs x < abs y ↔ natAbs x < natAbs y by rw [abs_eq_natAbs, abs_eq_natAbs, ofNat_lt] }

end Int

end AbsoluteValue
