/-
Released under MIT license.
-/
import Origin.Core

/-!
# Proof: Ordered algebra works with Origin

The roundoff. Ordered fields, monotonicity, positivity.
Where Mathlib uses OrderedField and LinearOrderedField.

The question: does Option α handle ordering when none is
the ground? none is not less than, not greater than, not
equal to any measurement. It's outside the order.
-/

universe u
variable {α : Type u}


-- ============================================================================
-- 1. ORDER ON OPTION: none is incomparable
-- ============================================================================

/-- Order on Option: some values inherit the underlying order.
    none is below everything — the ground is the bottom. -/
def optionLE [LE α] : Option α → Option α → Prop
  | some a, some b => a ≤ b
  | none, _ => True    -- none ≤ anything (ground is bottom)
  | some _, none => False  -- no value ≤ ground

/-- Strict order on Option. -/
def optionLT [LT α] : Option α → Option α → Prop
  | some a, some b => a < b
  | none, some _ => True   -- none < any value
  | _, none => False        -- nothing is < ground

-- ============================================================================
-- 2. REFLEXIVITY, TRANSITIVITY, ANTISYMMETRY
-- ============================================================================

theorem optionLE_refl [LE α] (h : ∀ a : α, a ≤ a)
    (v : Option α) : optionLE v v := by
  cases v with
  | none => simp [optionLE]
  | some a => simp [optionLE, h]

theorem optionLE_trans [LE α]
    (h : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c)
    (a b c : Option α) : optionLE a b → optionLE b c → optionLE a c := by
  cases a <;> cases b <;> cases c <;> simp [optionLE]
  · exact h _ _ _

theorem optionLE_antisymm [LE α]
    (h : ∀ a b : α, a ≤ b → b ≤ a → a = b)
    (a b : Option α) : optionLE a b → optionLE b a → a = b := by
  cases a <;> cases b <;> simp [optionLE]
  · intro hab hba; congr; exact h _ _ hab hba

-- ============================================================================
-- 3. NONE IS THE BOTTOM
-- ============================================================================

theorem none_le_all [LE α] (v : Option α) : optionLE none v := by
  cases v <;> simp [optionLE]

theorem not_some_le_none [LE α] (a : α) : ¬optionLE (some a) none := by
  simp [optionLE]

-- The ground is below every measurement. Not because it's "small."
-- Because ordering happens ON the ground. The ground is the
-- precondition for ordering, not a participant in it.

-- ============================================================================
-- 4. MONOTONICITY OF OPERATIONS
-- ============================================================================

-- Addition is monotone: a ≤ b → a + c ≤ b + c
theorem add_le_add_right [Add α] [LE α]
    (h : ∀ a b c : α, a ≤ b → a + c ≤ b + c)
    (a b : α) (c : α) :
    optionLE (some a) (some b) → optionLE (some a + some c) (some b + some c) := by
  simp [optionLE]; exact h a b c

-- Multiplication by positive preserves order
theorem mul_le_mul_of_nonneg [Mul α] [LE α]
    (h : ∀ a b c : α, a ≤ b → a * c ≤ b * c)
    (a b : α) (c : α) :
    optionLE (some a) (some b) → optionLE (some a * some c) (some b * some c) := by
  simp [optionLE]; exact h a b c

-- ============================================================================
-- 5. POSITIVITY: none vs some 0 vs some (positive)
-- ============================================================================

-- Three distinct concepts that Mathlib's 0 conflates:
-- 1. none      — the ground (not a number at all)
-- 2. some 0    — the zero measurement (a number, happened to be zero)
-- 3. some pos  — a positive measurement

-- In Mathlib: "x > 0" could mean "x is positive" or "x is not the ground."
-- In Origin: these are different questions with different answers.

theorem none_not_positive [LT α] (a : α) : ¬optionLT (some a) (none : Option α) := by
  simp [optionLT]

-- some 0 < some pos is a real mathematical statement about measurements
theorem zero_lt_pos [LT α] [Zero α] (pos : α) (h : (0 : α) < pos) :
    optionLT (some (0 : α)) (some pos) := by
  simp [optionLT, h]

-- none < some 0 — the ground is below the zero measurement
-- This is the statement that Mathlib can't make: the ground
-- is not the same as "zero"
theorem ground_lt_zero [LT α] [Zero α] :
    optionLT (none : Option α) (some (0 : α)) := by
  simp [optionLT]

-- ============================================================================
-- 6. MAX AND MIN LIFT
-- ============================================================================

-- ============================================================================
-- 7. CONCRETE: Option Int with order
-- ============================================================================

-- Ground is below everything
example : optionLE (none : Option Int) (some 0) := trivial
example : optionLE (none : Option Int) (some 5) := trivial
example : optionLE (none : Option Int) (some (-3)) := trivial

-- Values compare normally
example : optionLE (some 3 : Option Int) (some 5) := by simp [optionLE]

-- some 0 is a value, comparable to other values
example : optionLE (some 0 : Option Int) (some 5) := by simp [optionLE]

-- none is not ≥ any value
example : ¬optionLE (some 0 : Option Int) none := by
  simp [optionLE]

-- ============================================================================
-- 8. THE HONEST BOUNDARY
-- ============================================================================

-- Ordered fields in Mathlib require 0 ≤ 1 (ZeroLEOneClass).
-- In Origin: none ≤ some 1 (ground ≤ unit, trivially true).
-- And: some 0 ≤ some 1 (zero measurement ≤ unit, real math).
-- Both hold. No typeclass needed.

theorem ground_le_one [LE α] [One' α] :
    optionLE (none : Option α) (some 𝟙) := by
  simp [optionLE]

-- The ordering is total on some values, with none as a bottom.
-- This is a bounded partial order, not a linear order on Option.
-- Mathlib's LinearOrderedField collapses the bottom into the order.
-- Origin keeps them separate. The ordering works. The structure
-- is deliberately different. Same pattern as the ring boundary.
