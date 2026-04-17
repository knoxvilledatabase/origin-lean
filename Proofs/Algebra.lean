/-
Released under MIT license.
-/
import Origin.Core

/-!
# Proof: Algebra works with Origin

Every theorem below is a Mathlib Algebra theorem restated on Option α
and proved from Core. Each one closes with `simp`, `cases <;> simp`,
or a one-line proof. If it doesn't close, that's the honest boundary.

No Mathlib import. Just Core.
-/

universe u
variable {α β γ : Type u}

-- ============================================================================
-- 1. RING AXIOMS (Mathlib: Algebra.Ring.Basic)
-- ============================================================================

-- mul_comm: a * b = b * a
theorem mul_comm' [Mul α] (h : ∀ a b : α, a * b = b * a)
    (a b : Option α) : a * b = b * a :=
  option_mul_comm h a b

-- mul_assoc: (a * b) * c = a * (b * c)
theorem mul_assoc' [Mul α] (h : ∀ a b c : α, a * b * c = a * (b * c))
    (a b c : Option α) : a * b * c = a * (b * c) :=
  option_mul_assoc h a b c

-- add_comm: a + b = b + a
theorem add_comm' [Add α] (h : ∀ a b : α, a + b = b + a)
    (a b : Option α) : a + b = b + a :=
  option_add_comm h a b

-- add_assoc: (a + b) + c = a + (b + c)
theorem add_assoc' [Add α] (h : ∀ a b c : α, a + b + c = a + (b + c))
    (a b c : Option α) : a + b + c = a + (b + c) :=
  option_add_assoc h a b c

-- left_distrib: a * (b + c) = a * b + a * c
theorem left_distrib' [Add α] [Mul α]
    (h : ∀ a b c : α, a * (b + c) = a * b + a * c)
    (a b c : Option α) : a * (b + c) = a * b + a * c :=
  option_distrib h a b c

-- right_distrib: (a + b) * c = a * c + b * c
theorem right_distrib' [Add α] [Mul α]
    (h : ∀ a b c : α, (a + b) * c = a * c + b * c)
    (a b c : Option α) : (a + b) * c = a * c + b * c :=
  option_distrib_right h a b c

-- ============================================================================
-- 2. IDENTITY AND INVERSE (Mathlib: Algebra.Group.Basic)
-- ============================================================================

-- add_zero: a + 0 = a (none is additive identity on Option)
theorem add_zero' [Add α] (a : Option α) : a + none = a :=
  add_none_right a

-- zero_add: 0 + a = a
theorem zero_add' [Add α] (a : Option α) : none + a = a :=
  add_none_left a

-- one_mul: 1 * a = a
theorem one_mul' [Mul α] [One' α] (h : ∀ a : α, 𝟙 * a = a)
    (a : Option α) : some 𝟙 * a = a :=
  option_one_mul h a

-- mul_one: a * 1 = a
theorem mul_one' [Mul α] [One' α] (h : ∀ a : α, a * 𝟙 = a)
    (a : Option α) : a * some 𝟙 = a :=
  option_mul_one h a

-- neg_neg: -(-a) = a
theorem neg_neg' [Neg α] (h : ∀ a : α, -(-a) = a)
    (a : Option α) : -(-a) = a :=
  option_neg_neg h a

-- add_neg_cancel: a + (-a) = some 0 (stays in counting domain)
theorem add_neg_cancel' [Add α] [Neg α] (zero : α)
    (h : ∀ a : α, a + (-a) = zero) (a : α) :
    (some a : Option α) + -(some a) = some zero :=
  option_add_neg zero h a

-- mul_inv_cancel: a * a⁻¹ = some 1 (stays in counting domain)
theorem mul_inv_cancel' [Mul α] [Inv' α] [One' α]
    (h : ∀ a : α, a * a⁻¹' = 𝟙) (a : α) :
    (some a : Option α) * some (a⁻¹') = some 𝟙 :=
  option_mul_inv h a

-- ============================================================================
-- 3. ABSORPTION (Mathlib: Algebra.GroupWithZero — DISSOLVED)
-- ============================================================================

-- zero_mul: 0 * a = 0 (none absorbs — this is what GroupWithZero manages)
theorem zero_mul' [Mul α] (a : Option α) : none * a = none :=
  mul_none_left a

-- mul_zero: a * 0 = a (none absorbs)
theorem mul_zero' [Mul α] (a : Option α) : a * none = none :=
  mul_none_right a

-- The origin theorem: n * zero = zero (derived, not axiom)
theorem origin_int : ∀ n : Int, n * 0 = 0 :=
  fun n => origin 0 Int.add_right_neg Int.mul_add
    (fun a b => (Int.neg_mul_eq_mul_neg a b).symm) n

-- ============================================================================
-- 4. NEGATION LAWS (Mathlib: Algebra.Group.Basic)
-- ============================================================================

-- neg_mul: (-a) * b = -(a * b)
theorem neg_mul' [Mul α] [Neg α]
    (h : ∀ a b : α, (-a) * b = -(a * b))
    (a b : Option α) : (-a) * b = -(a * b) :=
  option_neg_mul h a b

-- mul_neg: a * (-b) = -(a * b)
theorem mul_neg' [Mul α] [Neg α]
    (h : ∀ a b : α, a * (-b) = -(a * b))
    (a b : Option α) : a * (-b) = -(a * b) :=
  option_mul_neg h a b

-- neg_mul_neg: (-a) * (-b) = a * b
theorem neg_mul_neg' [Mul α] [Neg α]
    (h : ∀ a b : α, (-a) * (-b) = a * b)
    (a b : Option α) : (-a) * (-b) = a * b :=
  option_neg_mul_neg h a b

-- neg_add: -(a + b) = -a + -b
theorem neg_add' [Add α] [Neg α]
    (h : ∀ a b : α, -(a + b) = -a + -b)
    (a b : Option α) : -(a + b) = -a + -b :=
  option_neg_add h a b

-- neg_none: -none = none (negating the ground gives the ground)
theorem neg_none' [Neg α] : -(none : Option α) = none := neg_none

-- ============================================================================
-- 5. NO ZERO DIVISORS (Mathlib: NoZeroDivisors — DISSOLVED)
-- ============================================================================

-- In Mathlib this requires a typeclass. In Origin it's structural.
-- If a * b = none, then a = none or b = none.
-- You can't reach the ground by multiplying parts.
theorem no_zero_divisors' [Mul α] {a b : Option α}
    (h : a * b = none) : a = none ∨ b = none :=
  option_mul_eq_none h

-- ============================================================================
-- 6. MAP FUNCTORIALITY (Mathlib: various)
-- ============================================================================

-- Option.map preserves composition
theorem map_comp' (f : α → β) (g : β → γ) (v : Option α) :
    Option.map g (Option.map f v) = Option.map (g ∘ f) v :=
  option_map_comp f g v

-- Option.map preserves identity
theorem map_id' (v : Option α) : Option.map id v = v := by
  cases v <;> simp

-- ============================================================================
-- 7. CONCRETE INSTANTIATION ON Int
-- ============================================================================

-- All ring axioms hold on Option Int via Core instances
example : (some 3 : Option Int) * some 5 = some 15 := rfl
example : (some 3 : Option Int) + some 5 = some 8 := rfl
example : -(some 3 : Option Int) = some (-3) := rfl
example : (none : Option Int) * some 5 = none := rfl
example : (some 0 : Option Int) * some 5 = some 0 := rfl
example : (some 0 : Option Int) ≠ (none : Option Int) := by simp

-- The critical distinction: some 0 ≠ none
-- some 0 is "we counted and got zero" (measurement)
-- none is "the ground" (wholeness)
-- This is what the 17 typeclasses were managing
theorem some_zero_ne_none : (some 0 : Option Int) ≠ none := by simp
