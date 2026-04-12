/-
Released under MIT license.
-/
import ValClass.Field

/-!
# Val α: Level 4 — ValOrderedField (Ordering)

Extends ValField with a total order compatible with the field operations.
The ordering lives within contents — origin has no order, container has no order.

Domains: Analysis, Topology, MeasureTheory, FunctionalAnalysis, Geometry,
Dynamics, InformationTheory.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- The Ordered Field Class
-- ============================================================================

class ValOrderedField (α : Type u) extends ValField α where
  leF : α → α → Prop
  le_refl : ∀ a : α, leF a a
  le_trans : ∀ a b c : α, leF a b → leF b c → leF a c
  le_antisymm : ∀ a b : α, leF a b → leF b a → a = b
  le_total : ∀ a b : α, leF a b ∨ leF b a
  add_le_add : ∀ a b c : α, leF a b → leF (addF a c) (addF b c)
  mul_pos : ∀ a b : α, leF zero a → leF zero b → leF zero (mulF a b)

-- ============================================================================
-- Ordering on Val α
-- ============================================================================

/-- Ordering on Val: only defined between contents of the same sort. -/
def valLE [ValOrderedField α] : Val α → Val α → Prop
  | contents a, contents b => ValOrderedField.leF a b
  | _, _ => False

/-- Strict ordering. -/
def valLT [ValOrderedField α] : Val α → Val α → Prop
  | contents a, contents b => ValOrderedField.leF a b ∧ a ≠ b
  | _, _ => False

-- ============================================================================
-- Lifted Ordering Laws
-- ============================================================================

theorem valLE_refl [ValOrderedField α] (a : α) :
    valLE (contents a) (contents a) := ValOrderedField.le_refl a

theorem valLE_trans [ValOrderedField α] (a b c : α)
    (hab : valLE (contents a) (contents b))
    (hbc : valLE (contents b) (contents c)) :
    valLE (contents a) (contents c) :=
  ValOrderedField.le_trans a b c hab hbc

theorem valLE_antisymm [ValOrderedField α] (a b : α)
    (hab : valLE (contents a) (contents b))
    (hba : valLE (contents b) (contents a)) :
    a = b :=
  ValOrderedField.le_antisymm a b hab hba

theorem valLE_total [ValOrderedField α] (a b : α) :
    valLE (contents a) (contents b) ∨ valLE (contents b) (contents a) :=
  ValOrderedField.le_total a b

-- ============================================================================
-- Absolute Value and Min/Max (as valMap/mul)
-- ============================================================================

abbrev valAbs [ValArith α] (absF : α → α) : Val α → Val α := valMap absF
abbrev valMin [ValArith α] (minF : α → α → α) : Val α → Val α → Val α := mul
abbrev valMax [ValArith α] (maxF : α → α → α) : Val α → Val α → Val α := mul

end Val
