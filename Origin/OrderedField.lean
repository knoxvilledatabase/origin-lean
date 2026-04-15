/-
Released under MIT license.
-/
import Origin.Field

/-!
# Origin OrderedField: Ordering on Option α

Val needed OrderedField.lean (79 lines) as Level 4 of a five-level
class hierarchy. Ordering lived within contents — origin and container
had no order.

Origin: ordering lives within Some. None (the whole) has no order.
The whole is not greater or lesser than anything — it is what the
ordering stands on. You don't compare the ground to the apples.
-/

universe u
variable {α : Type u}

-- ============================================================================
-- Ordering on Option: only defined between values
-- ============================================================================

/-- Ordering: only between values (Some). The whole (None) is outside
    the ordering — not less than, not greater than. Not ordered. -/
def oLE (leF : α → α → Prop) : Option α → Option α → Prop
  | some a, some b => leF a b
  | _, _ => False

/-- Strict ordering: less-or-equal and not equal. -/
def oLT (leF : α → α → Prop) : Option α → Option α → Prop
  | some a, some b => leF a b ∧ a ≠ b
  | _, _ => False

-- ============================================================================
-- Lifted Ordering Laws
-- ============================================================================

theorem oLE_refl
    (leF : α → α → Prop)
    (h : ∀ a : α, leF a a)
    (a : α) : oLE leF (some a) (some a) := h a

theorem oLE_trans
    (leF : α → α → Prop)
    (h : ∀ a b c : α, leF a b → leF b c → leF a c)
    (a b c : α)
    (hab : oLE leF (some a) (some b))
    (hbc : oLE leF (some b) (some c)) :
    oLE leF (some a) (some c) := h a b c hab hbc

theorem oLE_antisymm
    (leF : α → α → Prop)
    (h : ∀ a b : α, leF a b → leF b a → a = b)
    (a b : α)
    (hab : oLE leF (some a) (some b))
    (hba : oLE leF (some b) (some a)) :
    a = b := h a b hab hba

theorem oLE_total
    (leF : α → α → Prop)
    (h : ∀ a b : α, leF a b ∨ leF b a)
    (a b : α) :
    oLE leF (some a) (some b) ∨ oLE leF (some b) (some a) := h a b

-- ============================================================================
-- None is outside the ordering
-- ============================================================================

/-- The whole is not comparable to any value. -/
theorem oLE_none_left (leF : α → α → Prop) (b : Option α) :
    oLE leF none b = False := by cases b <;> rfl

theorem oLE_none_right (leF : α → α → Prop) (a : Option α) :
    oLE leF a none = False := by cases a <;> rfl

-- ============================================================================
-- Absolute Value and Min/Max
-- ============================================================================

/-- Absolute value: Option.map. None stays None. -/
def oAbs (absF : α → α) : Option α → Option α := Option.map absF

/-- Min/Max: liftBin₂ with the appropriate function. -/
def oMin (minF : α → α → α) : Option α → Option α → Option α
  | some a, some b => some (minF a b)
  | _, _ => none

def oMax (maxF : α → α → α) : Option α → Option α → Option α
  | some a, some b => some (maxF a b)
  | _, _ => none

-- ============================================================================
-- The Count
-- ============================================================================

-- Val/OrderedField.lean: 79 lines. Level 4 of 5.
-- Origin/OrderedField.lean: this file.
--
-- The ordering lives within Some (the parts). None (the whole) is
-- outside the ordering. You don't compare the ground to the apples.
-- You compare apples to apples. The ground is what the comparison
-- stands on.
