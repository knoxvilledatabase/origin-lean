/-
Extracted from Data/Int/Cast/Lemmas.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Cast of integers (additional theorems)

This file proves additional properties about the *canonical* homomorphism from
the integers into an additive group with a one (`Int.cast`),
particularly results involving algebraic homomorphisms or the order structure on `ℤ`
which were not available in the import dependencies of `Data.Int.Cast.Basic`.

## Main declarations

* `castAddHom`: `cast` bundled as an `AddMonoidHom`.
* `castRingHom`: `cast` bundled as a `RingHom`.
-/

assert_not_exists RelIso IsOrderedMonoid Field

open Additive Function Multiplicative Nat

variable {F ι α β : Type*}

namespace Int

def ofNatHom : ℕ →+* ℤ :=
  Nat.castRingHom ℤ

section cast

def castAddHom (α : Type*) [AddGroupWithOne α] : ℤ →+ α where
  toFun := Int.cast
  map_zero' := cast_zero
  map_add' := cast_add

section AddGroupWithOne

variable [AddGroupWithOne α]
