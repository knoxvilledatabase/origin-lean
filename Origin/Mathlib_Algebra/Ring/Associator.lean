/-
Extracted from Algebra/Ring/Associator.lean
Genuine: 3 of 4 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Associator in a ring

If `R` is a non-associative ring, then  `(x * y) * z - x * (y * z)` is called the `associator` of
ring elements `x y z : R`.

The associator vanishes exactly when `R` is associative.

We prove variants of this statement also for the `AddMonoidHom` bundled version of the associator,
as well as the bundled version of `mulLeft₃` and `mulRight₃`, the multiplications `(x * y) * z` and
`x * (y * z)`.
-/

variable {R : Type*}

section NonUnitalNonAssocRing

variable [NonUnitalNonAssocRing R]

def associator (x y z : R) : R := (x * y) * z - x * (y * z)

theorem associator_eq_zero_iff_associative :
    associator (R := R) = 0 ↔ Std.Associative (fun (x y : R) ↦ x * y) where
  mp h := ⟨fun x y z ↦ sub_eq_zero.mp <| congr_fun₃ h x y z⟩
  mpr h := by ext x y z; simp [associator, Std.Associative.assoc]

theorem associator_cocycle (a b c d : R) :
    a * associator b c d - associator (a * b) c d + associator a (b * c) d - associator a b (c * d)
    + (associator a b c) * d = 0 := by
  simp only [associator, mul_sub, sub_mul]
  abel1

open MulOpposite in
