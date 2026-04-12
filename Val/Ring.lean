/-
Released under MIT license.
-/
import Val.Arith

/-!
# Val α: Level 2 — ValRing (Ring Laws)

Extends ValArith with algebraic laws. All lifted laws proved once here,
inherited by every domain that says [ValRing α].

The proof pattern: cases <;> simp [op, Law]
Origin cases: simp closes them. Non-origin cases: the class law closes them.

Domains: GroupTheory, RepresentationTheory, CategoryTheory, HomologicalAlgebra,
Combinatorics, RingTheory, Condensed.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- The Ring Class
-- ============================================================================

class ValRing (α : Type u) extends ValArith α where
  mul_assoc : ∀ a b c : α, mulF (mulF a b) c = mulF a (mulF b c)
  add_assoc : ∀ a b c : α, addF (addF a b) c = addF a (addF b c)
  mul_comm : ∀ a b : α, mulF a b = mulF b a
  add_comm : ∀ a b : α, addF a b = addF b a
  left_distrib : ∀ a b c : α, mulF a (addF b c) = addF (mulF a b) (mulF a c)
  right_distrib : ∀ a b c : α, mulF (addF a b) c = addF (mulF a c) (mulF b c)
  neg_mul : ∀ a b : α, mulF (negF a) b = negF (mulF a b)
  mul_neg : ∀ a b : α, mulF a (negF b) = negF (mulF a b)
  neg_neg : ∀ a : α, negF (negF a) = a

-- ============================================================================
-- Lifted Ring Laws on Val α
-- ============================================================================

theorem val_mul_assoc [ValRing α] (a b c : Val α) :
    mul (mul a b) c = mul a (mul b c) := by
  cases a <;> cases b <;> cases c <;> simp [mul, ValRing.mul_assoc]

theorem val_add_assoc [ValRing α] (a b c : Val α) :
    add (add a b) c = add a (add b c) := by
  cases a <;> cases b <;> cases c <;> simp [add, ValRing.add_assoc]

theorem val_mul_comm [ValRing α] (a b : Val α) :
    mul a b = mul b a := by
  cases a <;> cases b <;> simp [mul, ValRing.mul_comm]

theorem val_add_comm [ValRing α] (a b : Val α) :
    add a b = add b a := by
  cases a <;> cases b <;> simp [add, ValRing.add_comm]

theorem val_left_distrib [ValRing α] (a b c : Val α) :
    mul a (add b c) = add (mul a b) (mul a c) := by
  cases a <;> cases b <;> cases c <;> simp [mul, add, ValRing.left_distrib]

theorem val_right_distrib [ValRing α] (a b c : Val α) :
    mul (add a b) c = add (mul a c) (mul b c) := by
  cases a <;> cases b <;> cases c <;> simp [mul, add, ValRing.right_distrib]

theorem val_neg_mul [ValRing α] (a b : Val α) :
    mul (neg a) b = neg (mul a b) := by
  cases a <;> cases b <;> simp [mul, neg, ValRing.neg_mul]

theorem val_mul_neg [ValRing α] (a b : Val α) :
    mul a (neg b) = neg (mul a b) := by
  cases a <;> cases b <;> simp [mul, neg, ValRing.mul_neg]

theorem val_neg_neg [ValRing α] (a : Val α) :
    neg (neg a) = a := by
  cases a <;> simp [neg, ValRing.neg_neg]

-- ============================================================================
-- Derived Laws (call the base, don't re-derive)
-- ============================================================================

theorem val_sub_mul [ValRing α] (a b c : Val α) :
    mul (add a (neg b)) c = add (mul a c) (neg (mul b c)) := by
  rw [val_right_distrib, val_neg_mul]

theorem val_mul_sub [ValRing α] (a b c : Val α) :
    mul a (add b (neg c)) = add (mul a b) (neg (mul a c)) := by
  rw [val_left_distrib, val_mul_neg]

theorem val_neg_comp_neg [ValRing α] (f g : Val α) :
    mul (neg f) (neg g) = mul f g := by
  rw [val_mul_neg, val_neg_mul, val_neg_neg]

-- ============================================================================
-- Preadditive Category Laws (one-liners calling the base)
-- ============================================================================

theorem preadditive_add_comp [ValRing α] (f f' g : Val α) :
    mul (add f f') g = add (mul f g) (mul f' g) :=
  val_right_distrib f f' g

theorem preadditive_comp_add [ValRing α] (f g g' : Val α) :
    mul f (add g g') = add (mul f g) (mul f g') :=
  val_left_distrib f g g'

theorem preadditive_neg_comp [ValRing α] (f g : Val α) :
    mul (neg f) g = neg (mul f g) :=
  val_neg_mul f g

theorem preadditive_comp_neg [ValRing α] (f g : Val α) :
    mul f (neg g) = neg (mul f g) :=
  val_mul_neg f g

-- ============================================================================
-- valMap Preserves Ring Structure
-- ============================================================================

theorem valMap_preserves_mul {β : Type u} [ValArith α] [ValArith β]
    (f : α → β)
    (hf : ∀ a b, f (ValArith.mulF a b) = ValArith.mulF (f a) (f b))
    (x y : Val α) :
    valMap f (mul x y) = mul (valMap f x) (valMap f y) := by
  cases x <;> cases y <;> simp [mul, valMap, hf]

theorem valMap_preserves_add {β : Type u} [ValArith α] [ValArith β]
    (f : α → β)
    (hf : ∀ a b, f (ValArith.addF a b) = ValArith.addF (f a) (f b))
    (x y : Val α) :
    valMap f (add x y) = add (valMap f x) (valMap f y) := by
  cases x <;> cases y <;> simp [add, valMap, hf]

theorem valMap_preserves_neg {β : Type u} [ValArith α] [ValArith β]
    (f : α → β)
    (hf : ∀ a, f (ValArith.negF a) = ValArith.negF (f a))
    (x : Val α) :
    valMap f (neg x) = neg (valMap f x) := by
  cases x <;> simp [neg, valMap, hf]

end Val
