/-
Released under MIT license.
-/
import Val.Ring

/-!
# Val α: Level 3 — ValField (Field Laws)

Extends ValRing with identity elements and inverses. Division is defined.
The critical distinction: `contents(zero) * contents(x) = contents(zero*x)` (arithmetic),
but `origin * contents(x) = origin` (absorption). The field lives inside contents.

Domains: FieldTheory, NumberTheory, LinearAlgebra, AlgebraicGeometry, Probability.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- The Field Class
-- ============================================================================

class ValField (α : Type u) extends ValRing α where
  one : α
  zero : α
  mul_one : ∀ a : α, mulF a one = a
  one_mul : ∀ a : α, mulF one a = a
  add_zero : ∀ a : α, addF a zero = a
  zero_add : ∀ a : α, addF zero a = a
  mul_inv : ∀ a : α, mulF a (invF a) = one
  inv_mul : ∀ a : α, mulF (invF a) a = one
  add_neg : ∀ a : α, addF a (negF a) = zero
  neg_add : ∀ a : α, addF (negF a) a = zero

-- ============================================================================
-- Lifted Field Laws on Val α
-- ============================================================================

theorem val_mul_one [ValField α] (a : Val α) :
    mul a (contents ValField.one) = a := by
  cases a <;> simp [mul, ValField.mul_one]

theorem val_one_mul [ValField α] (a : Val α) :
    mul (contents ValField.one) a = a := by
  cases a <;> simp [mul, ValField.one_mul]

theorem val_add_zero [ValField α] (a : Val α) :
    add a (contents ValField.zero) = a := by
  cases a <;> simp [add, ValField.add_zero]

theorem val_zero_add [ValField α] (a : Val α) :
    add (contents ValField.zero) a = a := by
  cases a <;> simp [add, ValField.zero_add]

theorem val_mul_inv [ValField α] (a : α) :
    mul (contents a) (inv (contents a)) = contents ValField.one := by
  simp [mul, inv, ValField.mul_inv]

theorem val_inv_mul [ValField α] (a : α) :
    mul (inv (contents a)) (contents a) = contents ValField.one := by
  simp [mul, inv, ValField.inv_mul]

theorem val_add_neg [ValField α] (a : α) :
    add (contents a) (neg (contents a)) = contents ValField.zero := by
  simp [add, neg, ValField.add_neg]

theorem val_neg_add [ValField α] (a : α) :
    add (neg (contents a)) (contents a) = contents ValField.zero := by
  simp [add, neg, ValField.neg_add]

-- ============================================================================
-- Division
-- ============================================================================

theorem val_fdiv_contents [ValField α] (a b : α) :
    fdiv (contents a) (contents b) = contents (ValArith.mulF a (ValArith.invF b)) := by
  simp [fdiv, mul, inv]

theorem val_fdiv_origin_left [ValField α] (b : Val α) :
    fdiv origin b = origin := by
  simp [fdiv, mul]

-- ============================================================================
-- Inverse Laws
-- ============================================================================

theorem val_inv_inv [ValField α]
    (h : ∀ a : α, ValArith.invF (ValArith.invF a) = a)
    (a : Val α) : inv (inv a) = a := by
  cases a <;> simp [inv, h]

end Val
