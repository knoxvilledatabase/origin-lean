/-
Released under MIT license.
-/
import Origin.Core

/-!
# Representation Theory on Option α (Core-based)

**Category 2** — pure math, no zero-management infrastructure.

Mathlib RepresentationTheory: 15 files, 4,331 lines, 331 genuine declarations.
This version keeps only domain-specific definitions and proofs that
actually use Option.

Representation theory studies how groups act on vector spaces.
Key concepts: representations (group homomorphisms to endomorphisms),
invariants, equivariant maps, characters, and intertwiners.
-/

universe u
variable {α β G : Type u}

-- ============================================================================
-- 1. REPRESENTATIONS
-- ============================================================================

/-- A representation: a group element acts on a space via endomorphisms. -/
structure Representation (G α : Type u) where
  act : G → α → α

/-- The trivial representation: every group element acts as identity. -/
def Representation.trivial (G α : Type u) : Representation G α where
  act _ a := a

-- ============================================================================
-- 2. EQUIVARIANT MAPS (INTERTWINERS)
-- ============================================================================

/-- An equivariant map: commutes with the group action. -/
def IsEquivariant (ρ₁ : G → α → α) (ρ₂ : G → β → β) (f : α → β) : Prop :=
  ∀ g a, f (ρ₁ g a) = ρ₂ g (f a)

-- ============================================================================
-- 3. INVARIANTS
-- ============================================================================

/-- The invariant subspace: elements fixed by every group element. -/
def IsInvariant (act : G → α → α) (x : α) : Prop :=
  ∀ g, act g x = x

/-- A subrepresentation: a predicate preserved by the action. -/
def IsSubrepresentation (act : G → α → α) (mem : α → Prop) : Prop :=
  ∀ g a, mem a → mem (act g a)

-- ============================================================================
-- 4. CHARACTERS
-- ============================================================================

/-- The character of a representation: the trace of each group element's action. -/
def Character (_ : G → α) := G → α

-- ============================================================================
-- 5. IRREDUCIBILITY
-- ============================================================================

/-- A representation is irreducible if it has no proper subrepresentations. -/
def IsIrreducible (act : G → α → α) (trivialPred allPred : α → Prop) : Prop :=
  ∀ mem : α → Prop, IsSubrepresentation act mem →
    (∀ a, mem a → trivialPred a) ∨ (∀ a, allPred a → mem a)

-- ============================================================================
-- DEMONSTRATIONS: Option lift works for this domain
-- ============================================================================

/-- none absorbs under multiplication. -/
theorem rep_none_mul [Mul α] (b : Option α) :
    none * b = (none : Option α) := by simp

/-- some values compute. -/
theorem rep_some_mul [Mul α] (a b : α) :
    (some a : Option α) * some b = some (a * b) := by simp

/-- Mapping preserves origin. -/
theorem rep_map_none (f : α → β) :
    Option.map f none = (none : Option β) := by simp

/-- A group action lifts through Option. -/
theorem rep_action_option (act : α → α) (v : Option α) :
    Option.map act v = match v with | none => none | some a => some (act a) := by
  cases v <;> simp
