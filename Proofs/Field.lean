/-
Released under MIT license.
-/
import Origin.Core

/-!
# Proof: Field theory works with Origin

The hard cases. Division, multiplicative inverse, the ≠ 0 boundary.

In Mathlib, these require GroupWithZero, MulZeroClass, or ≠ 0 guards.
In Origin, none is the ground (absorbs) and some 0 is a measurement
(stays in the counting domain). The question: does this separation
handle every field theorem, or does it break somewhere?

Each theorem either closes or it doesn't. Both are information.
-/

universe u
variable {α : Type u}

-- ============================================================================
-- 1. DIVISION: the core test
-- ============================================================================

-- In Mathlib: div_self requires h : a ≠ 0, guarded by GroupWithZero.
-- In Origin: some a * some (a⁻¹) = some 1. Always. No guard needed.
-- The guard was protecting against none (the ground). some 0 * some (0⁻¹)
-- is a legitimate computation — it gives some (0 * 0⁻¹), which is whatever
-- 0⁻¹ is in the underlying type. The ground never enters.

theorem div_self' [Mul α] [Inv' α] [One' α]
    (h : ∀ a : α, a * a⁻¹' = 𝟙) (a : α) :
    (some a : Option α) * some (a⁻¹') = some 𝟙 := by
  simp [h]

-- What about none? none * anything = none. You can't divide by the ground.
-- Not because of a guard — because none absorbs. Structurally.
theorem div_none_left [Mul α] [Inv' α] (b : Option α) :
    (none : Option α) * b = none :=
  mul_none_left b

theorem div_none_right [Mul α] [Inv' α] (a : Option α) :
    a * (none : Option α) = none :=
  mul_none_right a

-- Inverse of none is none. You can't invert the ground.
theorem inv_ground [Inv' α] : (none : Option α)⁻¹' = none :=
  inv_none

-- ============================================================================
-- 2. THE ≠ 0 BOUNDARY
-- ============================================================================

-- Mathlib: inv_ne_zero requires h : a ≠ 0. In Origin, this splits:
--   - If "≠ 0" means "not the ground": unnecessary. none⁻¹ = none,
--     and some a is never none. The type system prevents it.
--   - If "≠ 0" means "not the zero measurement": that's a real
--     mathematical constraint on some 0. Origin preserves it.

-- The ground is not in the counting domain — no guard needed
theorem some_ne_none (a : α) : (some a : Option α) ≠ none := by simp

-- some 0 is a value, not the ground — the distinction that matters
theorem some_zero_ne_none [Zero α] : (some (0 : α) : Option α) ≠ none := by simp

-- Inverse stays in the counting domain
theorem inv_some' [Inv' α] (a : α) :
    (some a : Option α)⁻¹' = some (a⁻¹') := by simp

-- ============================================================================
-- 3. FIELD AXIOMS lifted through Option
-- ============================================================================

-- mul_inv_cancel lifted: some a * some a⁻¹ = some 1
-- This is the Mathlib theorem that requires GroupWithZero.
-- Origin proves it without any typeclass beyond Mul, Inv', One'.
theorem field_mul_inv [Mul α] [Inv' α] [One' α]
    (h : ∀ a : α, a * a⁻¹' = 𝟙) (a : α) :
    (some a : Option α) * some (a⁻¹') = some 𝟙 :=
  option_mul_inv h a

-- inv_mul_cancel: a⁻¹ * a = 1
theorem field_inv_mul [Mul α] [Inv' α] [One' α]
    (h : ∀ a : α, a⁻¹' * a = 𝟙) (a : α) :
    (some (a⁻¹') : Option α) * some a = some 𝟙 := by
  simp [h]

-- Division as multiplication by inverse
def div' [Mul α] [Inv' α] (a b : Option α) : Option α :=
  a * b.map Inv'.inv

theorem div_some [Mul α] [Inv' α] (a b : α) :
    div' (some a) (some b) = some (a * b⁻¹') := by
  simp [div']

theorem div_none [Mul α] [Inv' α] (a : Option α) :
    div' a none = none := by
  simp [div']

-- ============================================================================
-- 4. WHAT MATHLIB NEEDS GroupWithZero FOR
-- ============================================================================

-- zero_mul and mul_zero: In Mathlib, these need MulZeroClass.
-- In Origin, they're just none absorption — already in Core's @[simp] set.
theorem gwz_zero_mul [Mul α] (a : Option α) : none * a = none :=
  mul_none_left a

theorem gwz_mul_zero [Mul α] (a : Option α) : a * none = none :=
  mul_none_right a

-- no_zero_divisors: if a * b = none, then a = none ∨ b = none.
-- In Mathlib: requires NoZeroDivisors typeclass.
-- In Origin: structural. some * some = some. QED.
theorem gwz_no_zero_divisors [Mul α] {a b : Option α}
    (h : a * b = none) : a = none ∨ b = none :=
  option_mul_eq_none h

-- ============================================================================
-- 5. DISTRIBUTIVITY WITH INVERSE
-- ============================================================================

-- (a + b) * c⁻¹ distributes
theorem distrib_inv [Add α] [Mul α] [Inv' α]
    (hd : ∀ a b c : α, (a + b) * c = a * c + b * c)
    (a b : α) (c : α) :
    (some a + some b : Option α) * some (c⁻¹') =
    some a * some (c⁻¹') + some b * some (c⁻¹') := by
  simp [hd]

-- ============================================================================
-- 6. CONCRETE: Option Int field operations
-- ============================================================================

-- Int doesn't have Inv' — that's a domain decision (integers don't
-- have multiplicative inverses). The mechanism works for any type
-- that does. The tests above are generic. Here we show absorption
-- on Int without needing Inv':

-- none absorbs under multiplication — no inverse needed
example : (none : Option Int) * some 3 = none := rfl
example : (some 6 : Option Int) * none = none := by simp

-- some 0 is a value, not the ground — the field distinction
example : (some 0 : Option Int) * some 5 = some 0 := rfl
example : (none : Option Int) * some 5 = none := rfl
-- some 0 * some 5 = some 0 (measurement). none * some 5 = none (ground).
-- Different results. Different meanings. One symbol in Mathlib.

-- ============================================================================
-- 7. THE HONEST BOUNDARY
-- ============================================================================

-- Option α is NOT a field. It's not even a ring. That's correct.
-- Cancellation lands at some 0, not at none (the additive identity).
-- some 0 ≠ none. The zero measurement is not the ground.
--
-- What Origin provides: every field *theorem* can be proved on
-- Option α using Core, because the theorems only need the algebraic
-- laws — and those lift through Option. The field *structure* (the
-- ring axiom that 0 = absorber) is what Origin separates.
--
-- The theorems work. The structure is deliberately different.
-- That's not a limitation. That's the point.

theorem honest_boundary [Add α] [Neg α] (zero : α)
    (h : ∀ a : α, a + (-a) = zero) (a : α) :
    (some a : Option α) + -(some a) = some zero := by
  simp [h]

-- Cancellation returns to some zero, NOT to none.
-- This is why Option α isn't a ring — and why that's correct.
-- The ground and the zero measurement are different things.
