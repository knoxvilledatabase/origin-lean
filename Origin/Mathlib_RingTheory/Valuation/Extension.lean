/-
Extracted from RingTheory/Valuation/Extension.lean
Genuine: 8 of 10 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Extension of Valuations

In this file, we define the typeclass for valuation extensions and prove basic facts about the
extension of valuations. Let `A` be an `R` algebra, equipped with valuations `vA` and `vR`
respectively. Here, the extension of a valuation means that the pullback of valuation `vA` to `R`
is equivalent to the valuation `vR` on `R`. We only require equivalence, not equality, of
valuations here.

Note that we do not require the ring map from `R` to `A` to be injective. This holds automatically
when `R` is a division ring and `A` is nontrivial.

A motivation for choosing the more flexible `Valuation.Equiv` rather than strict equality here is
to allow for possible normalization. As an example, consider a finite extension `K` of `ℚ_[p]`,
which is a discretely valued field. We may choose the valuation on `K` to be either:

1. the valuation where the uniformizer is mapped to one (more precisely, `-1` in `ℤᵐ⁰`) or

2. the valuation where `p` is mapped to one.

For the algebraic closure of `ℚ_[p]`, if we choose the valuation of `p` to be one, then the
restriction of this valuation to `K` equals the second valuation, but is only equivalent to the
first valuation. The flexibility of equivalence here allows us to develop theory for both cases
without first determining the normalizations once and for all.

## Main Definition

* `Valuation.HasExtension vR vA` : The valuation `vA` on `A` is an extension of the valuation
  `vR` on `R`.

## References

* [Bourbaki, Nicolas. *Commutative algebra*] Chapter VI §3, Valuations.
* <https://en.wikipedia.org/wiki/Valuation_(algebra)#Extension_of_valuations>

## Tags
Valuation, Extension of Valuations

-/

open Module

namespace Valuation

variable {R A ΓR ΓA : Type*} [CommRing R] [Ring A]
    [LinearOrderedCommMonoidWithZero ΓR] [LinearOrderedCommMonoidWithZero ΓA] [Algebra R A]
    (vR : Valuation R ΓR) (vA : Valuation A ΓA)

class HasExtension : Prop where
  /-- The valuation `vR` on `R` is equivalent to the comap of the valuation `vA` on `A` -/
  val_isEquiv_comap : vR.IsEquiv <| vA.comap (algebraMap R A)

namespace HasExtension

section algebraMap

variable [vR.HasExtension vA]

theorem val_map_le_iff (x y : R) : vA (algebraMap R A x) ≤ vA (algebraMap R A y) ↔ vR x ≤ vR y :=
  val_isEquiv_comap.symm x y

theorem val_map_lt_iff (x y : R) : vA (algebraMap R A x) < vA (algebraMap R A y) ↔ vR x < vR y := by
  simpa only [not_le] using ((val_map_le_iff vR vA _ _).not)

theorem val_map_eq_iff (x y : R) : vA (algebraMap R A x) = vA (algebraMap R A y) ↔ vR x = vR y :=
  (IsEquiv.eq_iff val_isEquiv_comap).symm

theorem val_map_le_one_iff (x : R) : vA (algebraMap R A x) ≤ 1 ↔ vR x ≤ 1 := by
  simpa only [map_one] using val_map_le_iff vR vA x 1

theorem val_map_lt_one_iff (x : R) : vA (algebraMap R A x) < 1 ↔ vR x < 1 := by
  simpa only [map_one, not_le] using (val_map_le_iff vR vA 1 x).not

theorem val_map_eq_one_iff (x : R) : vA (algebraMap R A x) = 1 ↔ vR x = 1 := by
  simpa only [le_antisymm_iff, map_one] using
    and_congr (val_map_le_iff vR vA x 1) (val_map_le_iff vR vA 1 x)

end algebraMap

-- INSTANCE (free from Core): id

section integer

variable {K : Type*} [Field K] [Algebra K A] {ΓR ΓA ΓK : Type*}
    [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓK]
    [LinearOrderedCommGroupWithZero ΓA] {vR : Valuation R ΓR} {vK : Valuation K ΓK}
    {vA : Valuation A ΓA} [vR.HasExtension vA]

theorem ofComapInteger (h : vA.integer.comap (algebraMap K A) = vK.integer) :
    vK.HasExtension vA where
  val_isEquiv_comap := by
    rw [isEquiv_iff_val_le_one]
    intro x
    simp_rw [← Valuation.mem_integer_iff, ← h, Subring.mem_comap, mem_integer_iff, comap_apply]

-- INSTANCE (free from Core): instAlgebraInteger
