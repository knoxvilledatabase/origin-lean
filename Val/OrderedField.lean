/-
Released under MIT license.
-/
import Val.Algebra

/-!
# Val α: Ordered Fields

Only contents are comparable. Origin and container are outside the
ordering entirely. If you're comparing, you're in contents.
The sort carries the answer.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Ordering: only contents are comparable
-- ============================================================================

def valLE (leF : α → α → Prop) : Val α → Val α → Prop
  | contents a, contents b => leF a b
  | _, _ => False

def valLT (ltF : α → α → Prop) : Val α → Val α → Prop
  | contents a, contents b => ltF a b
  | _, _ => False

-- ============================================================================
-- Partial Order (within contents)
-- ============================================================================

theorem valLE_refl (leF : α → α → Prop)
    (h : ∀ a : α, leF a a) (a : α) :
    valLE leF (contents a) (contents a) := h a

theorem valLE_trans (leF : α → α → Prop)
    (h : ∀ a b c : α, leF a b → leF b c → leF a c)
    (a b c : α) (hab : valLE leF (contents a) (contents b))
    (hbc : valLE leF (contents b) (contents c)) :
    valLE leF (contents a) (contents c) := h a b c hab hbc

theorem valLE_antisymm (leF : α → α → Prop)
    (h : ∀ a b : α, leF a b → leF b a → a = b)
    (a b : α) (hab : valLE leF (contents a) (contents b))
    (hba : valLE leF (contents b) (contents a)) :
    (contents a : Val α) = contents b := by
  congr; exact h a b hab hba

theorem valLE_total (leF : α → α → Prop)
    (h : ∀ a b : α, leF a b ∨ leF b a) (a b : α) :
    valLE leF (contents a) (contents b) ∨ valLE leF (contents b) (contents a) := h a b

-- ============================================================================
-- Origin and Container Outside the Order
-- ============================================================================

@[simp] theorem origin_not_le (leF : α → α → Prop) (x : Val α) :
    ¬ valLE leF origin x := by cases x <;> exact id

@[simp] theorem not_le_origin (leF : α → α → Prop) (x : Val α) :
    ¬ valLE leF x origin := by cases x <;> exact id

@[simp] theorem container_not_le (leF : α → α → Prop) (c : α) (x : Val α) :
    ¬ valLE leF (container c) x := by cases x <;> exact id

@[simp] theorem not_le_container (leF : α → α → Prop) (c : α) (x : Val α) :
    ¬ valLE leF x (container c) := by cases x <;> exact id

-- ============================================================================
-- Comparison Implies Contents
-- ============================================================================

theorem valLE_implies_contents (leF : α → α → Prop) (x y : Val α) (h : valLE leF x y) :
    ∃ a b, x = contents a ∧ y = contents b := by
  cases x with
  | origin => exact absurd h (origin_not_le leF y)
  | container c => exact absurd h (container_not_le leF c y)
  | contents a => cases y with
    | origin => exact absurd h (not_le_origin leF (contents a))
    | container c => exact absurd h (not_le_container leF c (contents a))
    | contents b => exact ⟨a, b, rfl, rfl⟩

-- If you're comparing, you're in contents. The sort is known.

-- ============================================================================
-- Absolute Value
-- ============================================================================

def valAbs (absF : α → α) : Val α → Val α
  | origin => origin
  | container a => container (absF a)
  | contents a => contents (absF a)

@[simp] theorem valAbs_origin (absF : α → α) : valAbs absF (origin : Val α) = origin := rfl
@[simp] theorem valAbs_contents (absF : α → α) (a : α) : valAbs absF (contents a) = contents (absF a) := rfl
@[simp] theorem valAbs_container (absF : α → α) (a : α) : valAbs absF (container a) = container (absF a) := rfl

theorem valAbs_ne_origin (absF : α → α) (a : α) :
    valAbs absF (contents a) ≠ (origin : Val α) := by simp

-- ============================================================================
-- Min / Max
-- ============================================================================

def valMin (minF : α → α → α) : Val α → Val α → Val α
  | contents a, contents b => contents (minF a b)
  | origin, _ => origin
  | _, origin => origin
  | container a, container b => container (minF a b)
  | container a, contents b => container (minF a b)
  | contents a, container b => container (minF a b)

def valMax (maxF : α → α → α) : Val α → Val α → Val α
  | contents a, contents b => contents (maxF a b)
  | origin, _ => origin
  | _, origin => origin
  | container a, container b => container (maxF a b)
  | container a, contents b => container (maxF a b)
  | contents a, container b => container (maxF a b)

theorem valMin_contents (minF : α → α → α) (a b : α) :
    ∃ c, valMin minF (contents a) (contents b) = contents c := ⟨_, rfl⟩

theorem valMax_contents (maxF : α → α → α) (a b : α) :
    ∃ c, valMax maxF (contents a) (contents b) = contents c := ⟨_, rfl⟩

end Val
