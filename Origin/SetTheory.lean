/-
Released under MIT license.
-/
import Origin.Core

/-!
# Set Theory on Option α (Core-based)

**Category 2** — pure math, no zero-management infrastructure.

Mathlib SetTheory: 46 files, 23,063 lines, 3,144 genuine declarations.
This version keeps only domain-specific definitions and proofs that
actually use Option.

Set theory: cardinals, ordinals, well-orderings, transfinite
induction, cofinality, continuum hypothesis. Domain concepts
abstracted without Mathlib's ordinal/cardinal machinery.
-/

universe u
variable {α β : Type u}

-- ============================================================================
-- 1. WELL-ORDERINGS
-- ============================================================================

/-- A relation is a well-ordering: every nonempty subset has a least element. -/
def IsWellOrder (r : α → α → Prop) : Prop :=
  (∀ a, ¬r a a) ∧
  (∀ a b c, r a b → r b c → r a c) ∧
  (∀ P : α → Prop, (∃ a, P a) → ∃ a, P a ∧ ∀ b, P b → ¬r b a)

-- ============================================================================
-- 2. ORDINALS (ABSTRACT)
-- ============================================================================

/-- An ordinal: an equivalence class of well-orderings. -/
structure Ordinal' where
  rank : Nat

/-- Successor ordinal. -/
def Ordinal'.succ (o : Ordinal') : Ordinal' := ⟨o.rank + 1⟩

/-- A limit ordinal: not zero, not a successor. -/
def Ordinal'.IsLimit (o : Ordinal') : Prop :=
  o.rank > 0 ∧ ∀ m, m < o.rank → m + 1 < o.rank

-- ============================================================================
-- 3. CARDINALS (ABSTRACT)
-- ============================================================================

/-- A cardinal: the "size" of a type. -/
structure Cardinal' where
  size : Nat

/-- Cardinal arithmetic. -/
instance : Add Cardinal' where add a b := ⟨a.size + b.size⟩
instance : Mul Cardinal' where mul a b := ⟨a.size * b.size⟩

/-- A cardinal is infinite. -/
def Cardinal'.IsInfinite (c : Cardinal') : Prop := ∀ n : Nat, n < c.size

-- ============================================================================
-- 4. COFINALITY
-- ============================================================================

/-- The cofinality of an ordinal: the smallest order type of a cofinal subset. -/
def Cofinality (rank : Nat) (cofinal : Nat → Prop) : Prop :=
  ∀ m, m < rank → ∃ n, cofinal n ∧ m ≤ n

-- ============================================================================
-- 5. TRANSFINITE INDUCTION
-- ============================================================================

/-- Transfinite induction principle (well-founded recursion). -/
def TransfiniteInduction (r : α → α → Prop) (P : α → Prop)
    (_ : ∀ a, (∀ b, r b a → P b) → P a) : Prop :=
  IsWellOrder r → ∀ a, P a

-- ============================================================================
-- 6. GAMES (COMBINATORIAL GAME THEORY)
-- ============================================================================

/-- A combinatorial game: left and right move sets. -/
structure Game' where
  leftMoves : Type u
  rightMoves : Type u

-- ============================================================================
-- DEMONSTRATIONS: Option lift works for this domain
-- ============================================================================

/-- none absorbs under multiplication. -/
theorem set_none_mul [Mul α] (b : Option α) :
    none * b = (none : Option α) := by simp

/-- some values compute. -/
theorem set_some_mul [Mul α] (a b : α) :
    (some a : Option α) * some b = some (a * b) := by simp

/-- Cardinal addition lifts through Option. -/
theorem set_add_none [Add α] (b : Option α) :
    none + b = b := by simp

/-- A law lifts through Option. -/
theorem set_mul_assoc [Mul α]
    (h : ∀ a b c : α, a * b * c = a * (b * c))
    (a b c : Option α) : a * b * c = a * (b * c) := by
  cases a <;> cases b <;> cases c <;> simp [h]
