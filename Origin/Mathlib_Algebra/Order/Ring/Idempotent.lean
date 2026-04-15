/-
Extracted from Algebra/Order/Ring/Idempotent.lean
Genuine: 4 of 13 | Dissolved: 0 | Infrastructure: 9
-/
import Origin.Core

/-!
# Boolean algebra structure on idempotents in a commutative (semi)ring

We show that the idempotent in a commutative ring form a Boolean algebra, with complement given
by `a ↦ 1 - a` and infimum given by multiplication. In a commutative semiring where subtraction
is not available, it is still true that pairs of elements `(a, b)` satisfying `a * b = 0` and
`a + b = 1` form a Boolean algebra (such elements are automatically idempotents, and such a pair
is uniquely determined by either `a` or `b`).
-/

variable {R : Type*}

-- INSTANCE (free from Core): [CommMonoid

lemma eq_of_mul_eq_add_eq_one [NonAssocSemiring R] (a : R) {b c : R}
    (mul : a * b = c * a) (add_ab : a + b = 1) (add_ac : a + c = 1) :
    b = c :=
  calc b = (a + c) * b := by rw [add_ac, one_mul]
       _ = c * (a + b) := by rw [add_mul, mul, mul_add]
       _ = c := by rw [add_ab, mul_one]

section CommSemiring

variable [CommSemiring R] {a b : {a : R × R // a.1 * a.2 = 0 ∧ a.1 + a.2 = 1}}

lemma mul_eq_zero_add_eq_one_ext_left (eq : a.1.1 = b.1.1) : a = b := by
  refine Subtype.ext <| Prod.ext_iff.mpr ⟨eq, eq_of_mul_eq_add_eq_one a.1.1 ?_ a.2.2 ?_⟩
  · rw [a.2.1, mul_comm, eq, b.2.1]
  · rw [eq, b.2.2]

lemma mul_eq_zero_add_eq_one_ext_right (eq : a.1.2 = b.1.2) : a = b := by
  refine Subtype.ext <| Prod.ext_iff.mpr ⟨eq_of_mul_eq_add_eq_one a.1.2 ?_ ?_ ?_, eq⟩
  · rw [mul_comm, a.2.1, eq, b.2.1]
  · rw [add_comm, a.2.2]
  · rw [add_comm, eq, b.2.2]

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

end CommSemiring

-- INSTANCE (free from Core): {S

-- INSTANCE (free from Core): {M

-- INSTANCE (free from Core): {M₀

section CommRing

variable [CommRing R]

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

def OrderIso.isIdempotentElemMulZeroAddOne :
    {a : R // IsIdempotentElem a} ≃o {a : R × R // a.1 * a.2 = 0 ∧ a.1 + a.2 = 1} where
  toFun a := ⟨(a, 1 - a), by simp_rw [mul_sub, mul_one, a.2.eq, sub_self], by rw [add_sub_cancel]⟩
  invFun a := ⟨a.1.1, (IsIdempotentElem.of_mul_add a.2.1 a.2.2).1⟩
  right_inv a := Subtype.ext <| Prod.ext rfl <| sub_eq_of_eq_add <| a.2.2.symm.trans (add_comm ..)
  map_rel_iff' := Iff.rfl

end CommRing
