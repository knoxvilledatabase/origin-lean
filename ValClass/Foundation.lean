/-
Released under MIT license.
-/

/-!
# Val α: Class-Based Foundation — Experiment

The same three constructors. The same four rules. But instead of passing
explicit function parameters to every theorem, the algebraic laws live
on classes. The sort dispatch stays on @[simp]. Two layers, each doing
what it's best at.

Test: does `by simp` still close origin cases when the operations come
from a class instance? If yes, this architecture replaces the explicit
parameter approach and dramatically reduces line count.
-/

universe u

-- ============================================================================
-- The Type (unchanged from original Foundation)
-- ============================================================================

inductive Val (α : Type u) where
  | origin : Val α
  | container : α → Val α
  | contents : α → Val α
deriving DecidableEq, Repr

namespace Val

variable {α : Type u}

-- ============================================================================
-- Base Class: ValArith — The Root of Everything
-- ============================================================================

/-- The arithmetic foundation. Every mathematical domain extends this.
    Carries the operations on α. The sort dispatch on Val α is separate. -/
class ValArith (α : Type u) where
  mulF : α → α → α
  addF : α → α → α
  negF : α → α
  invF : α → α

-- ============================================================================
-- Operations: dispatch on Val constructors, use class for α operations
-- ============================================================================

def mul [ValArith α] : Val α → Val α → Val α
  | origin, _                  => origin
  | _, origin                  => origin
  | container a, container b   => container (ValArith.mulF a b)
  | container a, contents b    => container (ValArith.mulF a b)
  | contents a, container b    => container (ValArith.mulF a b)
  | contents a, contents b     => contents (ValArith.mulF a b)

def add [ValArith α] : Val α → Val α → Val α
  | origin, _                  => origin
  | _, origin                  => origin
  | container a, container b   => container (ValArith.addF a b)
  | container a, contents b    => container (ValArith.addF a b)
  | contents a, container b    => container (ValArith.addF a b)
  | contents a, contents b     => contents (ValArith.addF a b)

def neg [ValArith α] : Val α → Val α
  | origin       => origin
  | container a  => container (ValArith.negF a)
  | contents a   => contents (ValArith.negF a)

def inv [ValArith α] : Val α → Val α
  | origin       => origin
  | container a  => container (ValArith.invF a)
  | contents a   => contents (ValArith.invF a)

-- ============================================================================
-- Sort Dispatch: @[simp] lemmas (same as original, but using class)
-- ============================================================================

-- mul
@[simp] theorem mul_origin_left [ValArith α] (a : Val α) :
    mul origin a = origin := by cases a <;> rfl

@[simp] theorem mul_origin_right [ValArith α] (a : Val α) :
    mul a origin = origin := by cases a <;> rfl

@[simp] theorem mul_contents_contents [ValArith α] (a b : α) :
    mul (contents a) (contents b) = contents (ValArith.mulF a b) := rfl

@[simp] theorem mul_container_container [ValArith α] (a b : α) :
    mul (container a) (container b) = container (ValArith.mulF a b) := rfl

@[simp] theorem mul_container_contents [ValArith α] (a b : α) :
    mul (container a) (contents b) = container (ValArith.mulF a b) := rfl

@[simp] theorem mul_contents_container [ValArith α] (a b : α) :
    mul (contents a) (container b) = container (ValArith.mulF a b) := rfl

-- add
@[simp] theorem add_origin_left [ValArith α] (a : Val α) :
    add origin a = origin := by cases a <;> rfl

@[simp] theorem add_origin_right [ValArith α] (a : Val α) :
    add a origin = origin := by cases a <;> rfl

@[simp] theorem add_contents_contents [ValArith α] (a b : α) :
    add (contents a) (contents b) = contents (ValArith.addF a b) := rfl

@[simp] theorem add_container_container [ValArith α] (a b : α) :
    add (container a) (container b) = container (ValArith.addF a b) := rfl

@[simp] theorem add_container_contents [ValArith α] (a b : α) :
    add (container a) (contents b) = container (ValArith.addF a b) := rfl

@[simp] theorem add_contents_container [ValArith α] (a b : α) :
    add (contents a) (container b) = container (ValArith.addF a b) := rfl

-- neg
@[simp] theorem neg_origin [ValArith α] : neg (origin : Val α) = origin := rfl
@[simp] theorem neg_container [ValArith α] (a : α) :
    neg (container a : Val α) = container (ValArith.negF a) := rfl
@[simp] theorem neg_contents [ValArith α] (a : α) :
    neg (contents a : Val α) = contents (ValArith.negF a) := rfl

-- inv
@[simp] theorem inv_origin [ValArith α] : inv (origin : Val α) = origin := rfl
@[simp] theorem inv_container [ValArith α] (a : α) :
    inv (container a : Val α) = container (ValArith.invF a) := rfl
@[simp] theorem inv_contents [ValArith α] (a : α) :
    inv (contents a : Val α) = contents (ValArith.invF a) := rfl

-- ============================================================================
-- Sort predicates and disjointness (unchanged)
-- ============================================================================

@[simp] theorem contents_ne_origin (a : α) : (contents a : Val α) ≠ origin := by intro h; cases h
@[simp] theorem container_ne_origin (a : α) : (container a : Val α) ≠ origin := by intro h; cases h
@[simp] theorem origin_ne_contents (a : α) : (origin : Val α) ≠ contents a := by intro h; cases h
@[simp] theorem origin_ne_container (a : α) : (origin : Val α) ≠ container a := by intro h; cases h

@[simp] theorem contents_inj (a b : α) :
    (contents a : Val α) = contents b ↔ a = b := by
  constructor
  · intro h; cases h; rfl
  · intro h; rw [h]

-- ============================================================================
-- ValMap (unchanged — doesn't need class, it's the generic functor)
-- ============================================================================

def valMap {β : Type u} (f : α → β) : Val α → Val β
  | origin => origin
  | container a => container (f a)
  | contents a => contents (f a)

@[simp] theorem valMap_origin {β : Type u} (f : α → β) :
    valMap f (origin : Val α) = origin := rfl
@[simp] theorem valMap_container {β : Type u} (f : α → β) (a : α) :
    valMap f (container a) = container (f a) := rfl
@[simp] theorem valMap_contents {β : Type u} (f : α → β) (a : α) :
    valMap f (contents a) = contents (f a) := rfl

-- ============================================================================
-- Ring Class: extends ValArith with laws
-- ============================================================================

/-- A Val-compatible ring. Carries the laws α must satisfy. -/
class ValRing (α : Type u) extends ValArith α where
  mul_assoc : ∀ a b c : α, mulF (mulF a b) c = mulF a (mulF b c)
  add_assoc : ∀ a b c : α, addF (addF a b) c = addF a (addF b c)
  mul_comm : ∀ a b : α, mulF a b = mulF b a
  add_comm : ∀ a b : α, addF a b = addF b a
  left_distrib : ∀ a b c : α, mulF a (addF b c) = addF (mulF a b) (mulF a c)
  right_distrib : ∀ a b c : α, mulF (addF a b) c = addF (mulF a c) (mulF b c)

-- ============================================================================
-- THE TEST: Lifted laws using class, proofs using simp
-- ============================================================================

/-- mul is associative on Val α. The class provides h, simp handles origin. -/
theorem val_mul_assoc [ValRing α] (a b c : Val α) :
    mul (mul a b) c = mul a (mul b c) := by
  cases a <;> cases b <;> cases c <;> simp [mul, ValRing.mul_assoc]

/-- add is associative on Val α. -/
theorem val_add_assoc [ValRing α] (a b c : Val α) :
    add (add a b) c = add a (add b c) := by
  cases a <;> cases b <;> cases c <;> simp [add, ValRing.add_assoc]

/-- mul is commutative on Val α. -/
theorem val_mul_comm [ValRing α] (a b : Val α) :
    mul a b = mul b a := by
  cases a <;> cases b <;> simp [mul, ValRing.mul_comm]

/-- add is commutative on Val α. -/
theorem val_add_comm [ValRing α] (a b : Val α) :
    add a b = add b a := by
  cases a <;> cases b <;> simp [add, ValRing.add_comm]

/-- Left distributivity on Val α. -/
theorem val_left_distrib [ValRing α] (a b c : Val α) :
    mul a (add b c) = add (mul a b) (mul a c) := by
  cases a <;> cases b <;> cases c <;> simp [mul, add, ValRing.left_distrib]

/-- Right distributivity on Val α. -/
theorem val_right_distrib [ValRing α] (a b c : Val α) :
    mul (add a b) c = add (mul a c) (mul b c) := by
  cases a <;> cases b <;> cases c <;> simp [mul, add, ValRing.right_distrib]

-- ============================================================================
-- Field Class: extends ValRing with inverse laws
-- ============================================================================

class ValField (α : Type u) extends ValRing α where
  one : α
  zero : α
  mul_one : ∀ a : α, mulF a one = a
  one_mul : ∀ a : α, mulF one a = a
  add_zero : ∀ a : α, addF a zero = a
  zero_add : ∀ a : α, addF zero a = a
  mul_inv : ∀ a : α, mulF a (invF a) = one
  add_neg : ∀ a : α, addF a (negF a) = zero

/-- mul identity on Val α. No explicit parameter needed. -/
theorem val_mul_one [ValField α] (a : Val α) :
    mul a (contents ValField.one) = a := by
  cases a <;> simp [mul, ValField.mul_one]

/-- add zero on Val α. -/
theorem val_add_zero [ValField α] (a : Val α) :
    add a (contents ValField.zero) = a := by
  cases a <;> simp [add, ValField.add_zero]

/-- mul inverse on Val α. Contents level only. -/
theorem val_mul_inv [ValField α] (a : α) :
    mul (contents a) (inv (contents a)) = contents ValField.one := by
  simp [mul, inv, ValField.mul_inv]

/-- add negation on Val α. Contents level only. -/
theorem val_add_neg [ValField α] (a : α) :
    add (contents a) (neg (contents a)) = contents ValField.zero := by
  simp [add, neg, ValField.add_neg]

-- ============================================================================
-- COMPARISON: Class approach vs explicit parameter approach
-- ============================================================================

-- EXPLICIT (old way — 3 parameters):
-- theorem mul_assoc_explicit (f : α → α → α)
--     (h : ∀ a b c, f (f a b) c = f a (f b c))
--     (a b c : Val α) : mul f (mul f a b) c = mul f a (mul f b c)

-- CLASS (new way — 0 parameters beyond the values):
-- theorem val_mul_assoc [ValRing α] (a b c : Val α) :
--     mul (mul a b) c = mul a (mul b c)

-- Savings per theorem: 2 lines of parameters. Across 56,815 theorems: ~113,000 lines.

-- ============================================================================
-- DOMAIN EXAMPLE: A domain theorem using class
-- ============================================================================

/-- Preadditive: add_comp = right_distrib. One line. No parameters. -/
theorem preadditive_add_comp [ValRing α] (f f' g : Val α) :
    mul (add f f') g = add (mul f g) (mul f' g) :=
  val_right_distrib f f' g

/-- Preadditive: comp_add = left_distrib. One line. No parameters. -/
theorem preadditive_comp_add [ValRing α] (f g g' : Val α) :
    mul f (add g g') = add (mul f g) (mul f g') :=
  val_left_distrib f g g'

-- ============================================================================
-- RESULT
-- ============================================================================
--
-- ✓ @[simp] fires correctly through class instances
-- ✓ cases <;> simp [mul, ValRing.mul_assoc] closes all 27 goals
-- ✓ Class provides the hypothesis, simp handles the dispatch
-- ✓ Domain theorems become one-liners calling the base
-- ✓ Zero explicit function parameters in any theorem statement
-- ✓ The proof pattern is identical: cases <;> simp [op, Law]
--
-- Line savings estimate:
--   Old: theorem mul_assoc (f : α → α → α) (h : ∀ a b c, ...) (a b c : Val α) : ...
--   New: theorem val_mul_assoc [ValRing α] (a b c : Val α) : ...
--   Per theorem: 1-3 lines saved (parameter declarations)
--   Across 56,815 B3 theorems: 50,000-170,000 lines saved
--
-- The architecture works. The class carries the algebra. The simp set
-- carries the dispatch. Two layers. Clean separation.

end Val
