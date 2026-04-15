/-
Extracted from Data/ZMod/QuotientRing.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# `ZMod n` and quotient groups / rings

This file relates `ZMod n` to the quotient ring `ℤ ⧸ Ideal.span {(n : ℤ)}`.

## Main definitions

- `ZMod.quotient_span_nat_equiv_zmod` and `ZMod.quotientSpanEquivZMod `:
  `ZMod n` is the ring quotient of `ℤ` by `n ℤ : Ideal.span {n}`
  (where `n : ℕ` and `n : ℤ` respectively)

## Tags

zmod, quotient ring, ideal quotient
-/

open QuotientAddGroup Set ZMod

variable (n : ℕ) {A R : Type*} [AddGroup A] [Ring R]

namespace Int

def quotientSpanNatEquivZMod : ℤ ⧸ Ideal.span {(n : ℤ)} ≃+* ZMod n :=
  (Ideal.quotEquivOfEq (ZMod.ker_intCastRingHom _)).symm.trans <|
    RingHom.quotientKerEquivOfRightInverse <|
      show Function.RightInverse ZMod.cast (Int.castRingHom (ZMod n)) from intCast_zmod_cast

def quotientSpanEquivZMod (a : ℤ) : ℤ ⧸ Ideal.span ({a} : Set ℤ) ≃+* ZMod a.natAbs :=
  (Ideal.quotEquivOfEq (span_natAbs a)).symm.trans (quotientSpanNatEquivZMod a.natAbs)
