/-
Released under MIT license.
-/
import Val.OrderedField

/-!
# Demo: The Math Actually Works

Concrete instances. Real computations. Run `lake build Val.Demo.Compute`
and see the results. This is not type-checking — this is evaluation.
-/

namespace Val

-- ============================================================================
-- Concrete Instance: Natural Numbers
-- ============================================================================

instance : ValArith Nat where
  mulF := Nat.mul
  addF := Nat.add
  negF := fun _ => 0    -- Nat has no negation
  invF := fun _ => 0    -- Nat has no inverse

-- ============================================================================
-- Basic Arithmetic: Does 2 + 3 = 5?
-- ============================================================================

/-- 2 + 3 = 5 within contents. -/
example : add (contents 2) (contents 3) = (contents 5 : Val Nat) := rfl

/-- 4 * 7 = 28 within contents. -/
example : mul (contents 4) (contents 7) = (contents 28 : Val Nat) := rfl

/-- 0 * 5 = 0 within contents. Zero is a quantity, not origin. -/
example : mul (contents 0) (contents 5) = (contents 0 : Val Nat) := rfl

-- ============================================================================
-- The Critical Distinction
-- ============================================================================

/-- contents(0) * contents(5) = contents(0): arithmetic. The sort stays contents. -/
example : mul (contents 0) (contents 5) = (contents 0 : Val Nat) := rfl

/-- origin * contents(5) = origin: absorption. The ground took it. -/
example : mul (origin : Val Nat) (contents 5) = origin := rfl

/-- These are NOT equal. contents(0) ≠ origin. -/
example : (contents 0 : Val Nat) ≠ origin := by simp

-- ============================================================================
-- Origin Absorption
-- ============================================================================

/-- origin + anything = origin -/
example : add (origin : Val Nat) (contents 42) = origin := rfl

/-- anything + origin = origin -/
example : add (contents 42 : Val Nat) origin = origin := rfl

/-- origin * anything = origin -/
example : mul (origin : Val Nat) (contents 999) = origin := rfl

/-- Chained: origin absorbs through any computation -/
example : add (mul (origin : Val Nat) (contents 3)) (contents 7) = origin := rfl

-- ============================================================================
-- Container Propagation
-- ============================================================================

/-- container carries the last known value through operations -/
example : mul (container 10 : Val Nat) (contents 3) = container 30 := rfl

/-- container * container = container -/
example : mul (container 5 : Val Nat) (container 6) = container 30 := rfl

/-- container + contents = container -/
example : add (container 5 : Val Nat) (contents 3) = container 8 := rfl

-- ============================================================================
-- Concrete Instance: Integers
-- ============================================================================

instance : ValArith Int where
  mulF := Int.mul
  addF := Int.add
  negF := Int.neg
  invF := fun _ => 0   -- Int has no multiplicative inverse

/-- Negative numbers work. -/
example : add (contents (3 : Int)) (contents (-5)) = contents (-2) := rfl

/-- Negation works. -/
example : neg (contents (7 : Int)) = contents (-7) := rfl

/-- Multiplication with negatives. -/
example : mul (contents (-3 : Int)) (contents 4) = contents (-12) := rfl

-- ============================================================================
-- ValMap: Sort-Preserving Functions
-- ============================================================================

/-- Double every value. -/
example : valMap (· * 2) (contents 5 : Val Nat) = contents 10 := rfl

/-- valMap preserves origin. -/
example : valMap (· * 2) (origin : Val Nat) = origin := rfl

/-- valMap preserves container. -/
example : valMap (· * 2) (container 5 : Val Nat) = container 10 := rfl

-- ============================================================================
-- Ring Laws: Verified on Concrete Values
-- ============================================================================

instance : ValRing Int where
  mulF := Int.mul
  addF := Int.add
  negF := Int.neg
  invF := fun _ => 0
  mul_assoc := fun a b c => Int.mul_assoc a b c
  add_assoc := fun a b c => Int.add_assoc a b c
  mul_comm := fun a b => Int.mul_comm a b
  add_comm := fun a b => Int.add_comm a b
  left_distrib := fun a b c => Int.mul_add a b c
  right_distrib := fun a b c => Int.add_mul a b c
  neg_mul := fun a b => Int.neg_mul a b
  mul_neg := fun a b => Int.mul_neg a b
  neg_neg := fun a => Int.neg_neg a

/-- Associativity on Val Int: (2 * 3) * 4 = 2 * (3 * 4) -/
example : mul (mul (contents (2 : Int)) (contents 3)) (contents 4) =
          mul (contents 2) (mul (contents 3) (contents 4)) :=
  val_mul_assoc (contents 2) (contents 3) (contents 4)

/-- Distributivity: 2 * (3 + 4) = 2*3 + 2*4 -/
example : mul (contents (2 : Int)) (add (contents 3) (contents 4)) =
          add (mul (contents 2) (contents 3)) (mul (contents 2) (contents 4)) :=
  val_left_distrib (contents 2) (contents 3) (contents 4)

/-- Commutativity: 5 * 7 = 7 * 5 -/
example : mul (contents (5 : Int)) (contents 7) =
          mul (contents 7) (contents 5) :=
  val_mul_comm (contents 5) (contents 7)

/-- Negation: -(-x) = x -/
example : neg (neg (contents (42 : Int))) = contents 42 :=
  val_neg_neg (contents 42)

-- ============================================================================
-- The Dissolution: ≠ 0 Hypotheses Don't Exist
-- ============================================================================

/-- In standard math: division requires a ≠ 0 guard.
    In Val: origin handles it. No hypothesis needed.
    contents(10) / contents(2) = contents(5) — arithmetic.
    contents(10) / origin = origin — absorption. No error. No guard. -/
example : mul (contents (10 : Int)) (origin : Val Int) = origin := rfl

/-- The sort tells you what you have BEFORE the operation executes.
    No runtime check. No exception. No NaN. The type prevents it. -/
example : (origin : Val Int) ≠ contents 0 := by simp

-- ============================================================================
-- Instantiation: One Instance Per Type, Every Theorem Follows
-- ============================================================================

-- The challenge: "A theorem about [ValRing α] for abstract α does not
-- give you a theorem about ℤ. You still need the instance."
--
-- Answer: the instance is 10 lines (ValRing Int above). After that,
-- EVERY ring theorem in the library works on Int automatically.
-- Mathlib writes map_mul separately for MonoidHom, MulEquiv, RingHom,
-- AlgHom, AlgEquiv, MulAction — 6 theorems. We write universal_hom_mul
-- once. The Int instance makes it work for Int. No per-theorem instantiation.

/-- After one ValRing Int instance, the preserved-mul theorem works.
    Here: negation distributes over multiplication (neg_mul from Ring.lean). -/
example : mul (neg (contents (3 : Int))) (contents 5) =
          neg (mul (contents 3) (contents 5)) :=
  val_neg_mul _ _

/-- val_mul_assoc works on Int. No extra instantiation needed. -/
example : mul (mul (contents (2 : Int)) (contents 3)) (contents 4) =
          mul (contents 2) (mul (contents 3) (contents 4)) :=
  val_mul_assoc _ _ _

/-- val_left_distrib works on Int. No extra instantiation needed. -/
example : mul (contents (2 : Int)) (add (contents 3) (contents 4)) =
          add (mul (contents 2) (contents 3)) (mul (contents 2) (contents 4)) :=
  val_left_distrib _ _ _

/-- val_neg_mul works on Int. No extra instantiation needed. -/
example : mul (neg (contents (3 : Int))) (contents 5) =
          neg (mul (contents 3) (contents 5)) :=
  val_neg_mul _ _

/-- val_sub_mul works on Int. No extra instantiation needed. -/
example : mul (add (contents (7 : Int)) (neg (contents 2))) (contents 3) =
          add (mul (contents 7) (contents 3)) (neg (mul (contents 2) (contents 3))) :=
  val_sub_mul _ _ _

-- Every theorem from Ring.lean works. Every theorem from Field.lean
-- will work once we provide ValField. One instance. All theorems.

-- ============================================================================
-- Multiple Types: Same Theorems, Different Instances
-- ============================================================================

-- Mathlib's concern: "You need per-type work."
-- Our answer: yes, ONE instance per type. Here are three.

-- Nat instance (already defined above, line 17)
-- Int instance (already defined above, line 116)

-- Bool instance: even Bool gets ring-like behavior
instance : ValArith Bool where
  mulF := Bool.and
  addF := Bool.xor
  negF := Bool.not
  invF := Bool.not

/-- Bool arithmetic through Val. -/
example : mul (contents true) (contents false) = (contents false : Val Bool) := rfl
example : add (contents true) (contents true) = (contents false : Val Bool) := rfl
example : mul (origin : Val Bool) (contents true) = origin := rfl

-- String instance: even strings work
instance : ValArith String where
  mulF := String.append
  addF := String.append
  negF := fun s => s  -- strings have no meaningful negation
  invF := fun s => s

/-- String concatenation through Val. -/
example : mul (contents "hello") (contents " world") = (contents "hello world" : Val String) := rfl
example : mul (origin : Val String) (contents "test") = origin := rfl

-- The pattern: define the instance ONCE, every Val operation works on that type.
-- Three types. Three instances. Every operation dispatches correctly.
-- The sort (origin/container/contents) is orthogonal to the type.

-- ============================================================================
-- RESULT
-- ============================================================================
--
-- Every example above is `rfl` or a one-liner calling the base.
-- Every example computes to a concrete value.
-- The Lean kernel verified every line.
--
-- One instance per type. Every theorem follows. No per-theorem instantiation.
-- contents(0) is zero the quantity. origin is the absence.
-- They are different constructors. The ambiguity doesn't exist.

end Val
