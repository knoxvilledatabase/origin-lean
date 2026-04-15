/-
Extracted from Algebra/Ring/Action/Basic.lean
Genuine: 4 | Conflates: 0 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core
import Mathlib.Algebra.GroupWithZero.Action.End
import Mathlib.Algebra.Ring.Hom.Defs

/-!
# Group action on rings

This file defines the typeclass of monoid acting on semirings `MulSemiringAction M R`,
and the corresponding typeclass of invariant subrings.

Note that `Algebra` does not satisfy the axioms of `MulSemiringAction`.

## Implementation notes

There is no separate typeclass for group acting on rings, group acting on fields, etc.
They are all grouped under `MulSemiringAction`.

## Tags

group action, invariant subring

-/

universe u v

class MulSemiringAction (M : Type u) (R : Type v) [Monoid M] [Semiring R] extends
  DistribMulAction M R where
  /-- Multipliying `1` by a scalar gives `1` -/
  smul_one : ∀ g : M, (g • (1 : R) : R) = 1
  /-- Scalar multiplication distributes across multiplication -/
  smul_mul : ∀ (g : M) (x y : R), g • (x * y) = g • x * g • y

section Semiring

variable (M N : Type*) [Monoid M] [Monoid N]

variable (R : Type v) [Semiring R]

instance (priority := 100) MulSemiringAction.toMulDistribMulAction
    (M R) {_ : Monoid M} {_ : Semiring R} [h : MulSemiringAction M R] :
    MulDistribMulAction M R :=
  { h with }

@[simps!]
def MulSemiringAction.toRingHom [MulSemiringAction M R] (x : M) : R →+* R :=
  { MulDistribMulAction.toMonoidHom R x, DistribMulAction.toAddMonoidHom R x with }

theorem toRingHom_injective [MulSemiringAction M R] [FaithfulSMul M R] :
    Function.Injective (MulSemiringAction.toRingHom M R) := fun _ _ h =>
  eq_of_smul_eq_smul fun r => RingHom.ext_iff.1 h r

instance RingHom.applyMulSemiringAction : MulSemiringAction (R →+* R) R where
  smul := (· <| ·)
  smul_one := map_one
  smul_mul := map_mul
  smul_zero := RingHom.map_zero
  smul_add := RingHom.map_add
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp]
protected theorem RingHom.smul_def (f : R →+* R) (a : R) : f • a = f a :=
  rfl

instance RingHom.applyFaithfulSMul : FaithfulSMul (R →+* R) R :=
  ⟨fun {_ _} h => RingHom.ext h⟩

section

variable {M N}

abbrev MulSemiringAction.compHom (f : N →* M) [MulSemiringAction M R] : MulSemiringAction N R :=
  { DistribMulAction.compHom R f, MulDistribMulAction.compHom R f with }

end

section SimpLemmas

attribute [simp] smul_one smul_mul' smul_zero smul_add

end SimpLemmas

end Semiring
