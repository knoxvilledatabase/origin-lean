/-
Extracted from Algebra/Ring/GrindInstances.lean
Genuine: 1 of 5 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Instances for `grind`.
-/

open Lean

variable (α : Type*)

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

theorem Semiring.toGrindSemiring_ofNat [Semiring α] (n : ℕ) :
    @OfNat.ofNat α n (Lean.Grind.Semiring.ofNat n) = n.cast := by
  match n with
  | 0 => simp
  | 1 => simp
  | n + 2 => rfl

attribute [local instance] Grind.Semiring.natCast Grind.Ring.intCast in

example (s : Grind.CommRing α) : CommRing α :=

  { s with

    zero_add := Grind.AddCommMonoid.zero_add

    right_distrib := Grind.Semiring.right_distrib

    mul_zero := Grind.Semiring.mul_zero

    one_mul := Grind.Semiring.one_mul

    nsmul := nsmulRec

    zsmul := zsmulRec

    npow := npowRec

    natCast := Nat.cast

    natCast_zero := Grind.Semiring.natCast_zero

    natCast_succ n := Grind.Semiring.natCast_succ n

    intCast := Int.cast

    intCast_ofNat := Grind.Ring.intCast_natCast

    intCast_negSucc n := by

      rw [Int.negSucc_eq, Grind.Ring.intCast_neg,

        Grind.Ring.intCast_natCast_add_one, Grind.Semiring.natCast_succ] }

example : (inferInstance : Lean.Grind.Semiring Nat) =

    (Lean.Grind.CommSemiring.toSemiring : Lean.Grind.Semiring Nat) := rfl

example : (inferInstance : Lean.Grind.Semiring UInt8) =

    (Lean.Grind.CommSemiring.toSemiring : Lean.Grind.Semiring UInt8) := rfl
