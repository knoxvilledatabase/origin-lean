/-
Extracted from Data/ZMod/QuotientGroup.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# `ZMod n` and quotient groups / rings

This file relates `ZMod n` to the quotient group `ℤ / AddSubgroup.zmultiples (n : ℤ)`.

## Main definitions

- `ZMod.quotientZMultiplesNatEquivZMod` and `ZMod.quotientZMultiplesEquivZMod`:
  `ZMod n` is the group quotient of `ℤ` by `n ℤ := AddSubgroup.zmultiples (n)`,
  (where `n : ℕ` and `n : ℤ` respectively)
- `ZMod.lift n f` is the map from `ZMod n` induced by `f : ℤ →+ A` that maps `n` to `0`.

## Tags

zmod, quotient group
-/

assert_not_exists Ideal TwoSidedIdeal

open QuotientAddGroup Set ZMod

open scoped IsMulCommutative

variable (n : ℕ) {A R : Type*} [AddGroup A] [Ring R]

namespace Int

def quotientZMultiplesNatEquivZMod : ℤ ⧸ AddSubgroup.zmultiples (n : ℤ) ≃+ ZMod n :=
  (quotientAddEquivOfEq (ZMod.ker_intCastAddHom _)).symm.trans <|
    quotientKerEquivOfRightInverse (Int.castAddHom (ZMod n)) cast intCast_zmod_cast

def quotientZMultiplesEquivZMod (a : ℤ) : ℤ ⧸ AddSubgroup.zmultiples a ≃+ ZMod a.natAbs :=
  (quotientAddEquivOfEq (zmultiples_natAbs a)).symm.trans (quotientZMultiplesNatEquivZMod a.natAbs)
