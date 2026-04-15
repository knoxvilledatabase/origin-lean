/-
Extracted from RingTheory/Ideal/Quotient/Defs.lean
Genuine: 2 of 11 | Dissolved: 0 | Infrastructure: 9
-/
import Origin.Core

/-!
# Ideal quotients

This file defines ideal quotients as a special case of submodule quotients and proves some basic
results about these quotients.

See `Algebra.RingQuot` for quotients of non-commutative rings.

## Main definitions

- `Ideal.instHasQuotient`: the quotient of a commutative ring `R` by an ideal `I : Ideal R`
- `Ideal.Quotient.commRing`: the ring structure of the ideal quotient
- `Ideal.Quotient.mk`: map an element of `R` to the quotient `R ⧸ I`
- `Ideal.Quotient.lift`: turn a map `R → S` into a map `R ⧸ I → S`
- `Ideal.quotEquivOfEq`: quotienting by equal ideals gives isomorphic rings
-/

universe u v w

namespace Ideal

open Set

variable {R : Type u} [Ring R] (I J : Ideal R) {a b : R}

variable {S : Type v}

-- INSTANCE (free from Core): instHasQuotient

-- INSTANCE (free from Core): {R}

namespace Quotient

variable {I} {x y : R}

-- INSTANCE (free from Core): one

set_option backward.isDefEq.respectTransparency false in

protected def ringCon (I : Ideal R) [I.IsTwoSided] : RingCon R where
  __ := QuotientAddGroup.con I.toAddSubgroup
  mul' {a₁ b₁ a₂ b₂} h₁ h₂ := by
    rw [Submodule.quotientRel_def] at h₁ h₂ ⊢
    exact mul_sub_mul_mem I h₁ h₂

-- INSTANCE (free from Core): ring

-- INSTANCE (free from Core): semiring

-- INSTANCE (free from Core): commSemiring

-- INSTANCE (free from Core): {R}

-- INSTANCE (free from Core): commRing

variable [I.IsTwoSided]

example : (ring I).toAddCommGroup = Submodule.Quotient.addCommGroup I := rfl

variable (I) in

def mk : R →+* R ⧸ I where
  toFun a := Submodule.Quotient.mk a
  map_zero' := rfl
  map_one' := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

-- INSTANCE (free from Core): :
