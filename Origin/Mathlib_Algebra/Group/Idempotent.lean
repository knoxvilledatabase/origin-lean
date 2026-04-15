/-
Extracted from Algebra/Group/Idempotent.lean
Genuine: 6 of 8 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Idempotents

This file defines idempotents for an arbitrary multiplication and proves some basic results,
including:

* `IsIdempotentElem.mul_of_commute`: In a semigroup, the product of two commuting idempotents is
  an idempotent;
* `IsIdempotentElem.pow_succ_eq`: In a monoid `a ^ (n+1) = a` for `a` an idempotent and `n` a
  natural number.

## Tags

projection, idempotent
-/

assert_not_exists GroupWithZero

variable {M N S : Type*}

def IsIdempotentElem [Mul M] (a : M) : Prop := a * a = a

namespace IsIdempotentElem

section Mul

variable [Mul M] {a : M}

lemma of_isIdempotent [Std.IdempotentOp (α := M) (· * ·)] (a : M) : IsIdempotentElem a :=
  Std.IdempotentOp.idempotent a

lemma eq (ha : IsIdempotentElem a) : a * a = a := ha

end Mul

section Semigroup

variable [Semigroup S] {a b : S}

lemma mul_of_commute (hab : Commute a b) (ha : IsIdempotentElem a) (hb : IsIdempotentElem b) :
    IsIdempotentElem (a * b) := by rw [IsIdempotentElem, hab.symm.mul_mul_mul_comm, ha.eq, hb.eq]

end Semigroup

section CommSemigroup

variable [CommSemigroup S] {a b : S}

lemma mul (ha : IsIdempotentElem a) (hb : IsIdempotentElem b) : IsIdempotentElem (a * b) :=
  ha.mul_of_commute (.all ..) hb

end CommSemigroup

section MulOneClass

variable [MulOneClass M] {a : M}

lemma one : IsIdempotentElem (1 : M) := mul_one _

-- INSTANCE (free from Core): :
