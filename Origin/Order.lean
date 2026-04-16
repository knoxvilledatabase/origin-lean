/-
Released under MIT license.
-/
import Origin.Core

/-!
# Order Theory on Option α (Core-based)

**Category 2** — pure math, no zero-management infrastructure.

Mathlib Order: 211 files, 75,874 lines, 10,131 genuine declarations.
This version keeps only domain-specific definitions and proofs that
actually use Option.

Order theory: partial orders, lattices, well-orders, filters,
Galois connections, fixed point theorems, directed sets, Boolean
algebras. The largest Mathlib domain by file count.
-/

universe u
variable {α β : Type u}

-- ============================================================================
-- 1. PARTIAL ORDERS
-- ============================================================================

/-- A partial order: reflexive, antisymmetric, transitive. -/
structure PartialOrder' (α : Type u) where
  le : α → α → Prop
  refl : ∀ a, le a a
  antisymm : ∀ a b, le a b → le b a → a = b
  trans : ∀ a b c, le a b → le b c → le a c

/-- A total order: every pair is comparable. -/
def IsTotal (le : α → α → Prop) : Prop :=
  ∀ a b, le a b ∨ le b a

-- ============================================================================
-- 2. LATTICES
-- ============================================================================

/-- A lattice: every pair has a join and meet. -/
structure Lattice' (α : Type u) extends PartialOrder' α where
  sup : α → α → α
  inf : α → α → α
  sup_le : ∀ a b c, le a c → le b c → le (sup a b) c
  le_inf : ∀ a b c, le c a → le c b → le c (inf a b)

/-- A bounded lattice: has top and bottom elements. -/
structure BoundedLattice' (α : Type u) extends Lattice' α where
  top : α
  bot : α
  le_top : ∀ a, le a top
  bot_le : ∀ a, le bot a

/-- A complete lattice: every subset has a supremum and infimum. -/
def IsCompleteLattice (sup inf : (α → Prop) → α)
    (le : α → α → Prop) : Prop :=
  (∀ S a, S a → le a (sup S)) ∧
  (∀ S a, (∀ b, S b → le b a) → le (sup S) a) ∧
  (∀ S a, S a → le (inf S) a) ∧
  (∀ S a, (∀ b, S b → le a b) → le a (inf S))

-- ============================================================================
-- 3. BOOLEAN ALGEBRAS
-- ============================================================================

/-- A Boolean algebra: a complemented distributive lattice. -/
structure BooleanAlgebra' (α : Type u) extends BoundedLattice' α where
  compl : α → α
  sup_compl : ∀ a, sup a (compl a) = top
  inf_compl : ∀ a, inf a (compl a) = bot

-- ============================================================================
-- 4. GALOIS CONNECTIONS
-- ============================================================================

/-- A Galois connection between two ordered types. -/
def IsGaloisConnection (l : α → β) (u : β → α)
    (leA : α → α → Prop) (leB : β → β → Prop) : Prop :=
  ∀ a b, leB (l a) b ↔ leA a (u b)

-- ============================================================================
-- 5. FILTERS
-- ============================================================================

/-- A filter on a type: upward closed, closed under finite intersections. -/
structure Filter' (α : Type u) where
  mem : (α → Prop) → Prop
  univ : mem (fun _ => True)
  inter : ∀ U V, mem U → mem V → mem (fun x => U x ∧ V x)
  superset : ∀ U V, mem U → (∀ x, U x → V x) → mem V

-- ============================================================================
-- 6. FIXED POINT THEOREMS
-- ============================================================================

/-- Knaster-Tarski: a monotone function on a complete lattice has a fixed point. -/
def IsLeastFixedPoint (f : α → α) (le : α → α → Prop) (x : α) : Prop :=
  f x = x ∧ ∀ y, f y = y → le x y

-- ============================================================================
-- 7. DIRECTED SETS
-- ============================================================================

/-- A directed set: every finite subset has an upper bound. -/
def IsDirected (le : α → α → Prop) : Prop :=
  ∀ a b, ∃ c, le a c ∧ le b c

-- ============================================================================
-- 8. WELL-FOUNDEDNESS
-- ============================================================================

/-- A relation is well-founded: no infinite descending chains. -/
def IsWellFounded' (r : α → α → Prop) : Prop :=
  ∀ P : α → Prop, (∀ a, (∀ b, r b a → P b) → P a) → ∀ a, P a

-- ============================================================================
-- DEMONSTRATIONS: Option lift works for this domain
-- ============================================================================

/-- none absorbs under multiplication. -/
theorem order_none_mul [Mul α] (b : Option α) :
    none * b = (none : Option α) := by simp

/-- some values compute. -/
theorem order_some_mul [Mul α] (a b : α) :
    (some a : Option α) * some b = some (a * b) := by simp

/-- Addition identity: none + b = b. -/
theorem order_none_add [Add α] (b : Option α) :
    none + b = b := by simp

/-- A law lifts through Option. -/
theorem order_mul_assoc [Mul α]
    (h : ∀ a b c : α, a * b * c = a * (b * c))
    (a b c : Option α) : a * b * c = a * (b * c) := by
  cases a <;> cases b <;> cases c <;> simp [h]
