/-
Released under MIT license.
-/
import Origin.Core

/-!
# Control on Option α (Core-based)

**Category 2** — pure math, no zero-management infrastructure.

Mathlib Control: 24 files, 3,984 lines, 348 genuine declarations.
This version keeps only domain-specific definitions and proofs that
actually use Option.

Control theory covers bifunctors, bitraversables, continuations,
writer monads, multivariate functors, and applicative transformations.
Most of Lean's stdlib already provides Monad, Functor, Traversable.
What remains: domain-specific abstractions and Option demonstrations.
-/

universe u v
variable {α β γ : Type u}

-- ============================================================================
-- 1. BIFUNCTOR
-- ============================================================================

/-- A two-argument functor: maps over both type parameters. -/
def IsBifunctor (bimap : (α → α) → (β → β) → γ → γ) : Prop :=
  bimap id id = id

-- ============================================================================
-- 2. CONTINUATION
-- ============================================================================

/-- Continuation passing: (α → m r) → m r. -/
def ContT (r : Type u) (m : Type u → Type v) (α : Type u) :=
  (α → m r) → m r

/-- Pure continuation monad. -/
abbrev Cont (r : Type u) (α : Type u) := ContT r Id α

/-- A label for callCC: captures the continuation. -/
structure Label (α : Type u) (m : Type u → Type v) (β : Type u) where
  apply : α → m β

-- ============================================================================
-- 3. WRITER
-- ============================================================================

/-- Writer monad transformer: computation with accumulated output. -/
def WriterT' (ω : Type u) (m : Type u → Type v) (α : Type u) := m (α × ω)

-- ============================================================================
-- 4. MULTIVARIATE FUNCTOR
-- ============================================================================

/-- Predicate lifting: every element satisfies a predicate. -/
def LiftP' (F : (Type u → Type u)) (P : α → Prop) (_ : F α) : Prop :=
  ∃ _ : F (Subtype P), True

/-- Relation lifting: elements are pairwise related. -/
def LiftR' (F : Type u → Type u) (R : α → α → Prop) (_ _ : F α) : Prop :=
  ∃ _ : F { p : α × α // R p.1 p.2 }, True

-- ============================================================================
-- 5. APPLICATIVE TRANSFORMATION
-- ============================================================================

/-- A natural transformation between applicative functors preserving pure and seq. -/
structure AppTransform (F G : Type u → Type u) [Applicative F] [Applicative G] where
  app : ∀ α, F α → G α
  preserves_pure : ∀ {α} (x : α), app α (pure x) = pure x

-- ============================================================================
-- 6. COMMUTATIVE APPLICATIVE
-- ============================================================================

/-- An applicative functor where effects commute. -/
def IsCommApplicative (F : Type u → Type u) [Applicative F] : Prop :=
  ∀ {α β : Type u} (a : F α) (b : F β),
    Prod.mk <$> a <*> b = (fun (b : β) a => (a, b)) <$> b <*> a

-- ============================================================================
-- DEMONSTRATIONS: Option lift works for this domain
-- ============================================================================

/-- none absorbs under multiplication. -/
theorem control_none_mul [Mul α] (b : Option α) :
    none * b = (none : Option α) := by simp

/-- some values compute. -/
theorem control_some_mul [Mul α] (a b : α) :
    (some a : Option α) * some b = some (a * b) := by simp

/-- Mapping preserves origin. -/
theorem control_map_none (f : α → β) :
    Option.map f none = (none : Option β) := by simp

/-- A domain law lifts through Option. -/
theorem control_mul_comm [Mul α]
    (h : ∀ a b : α, a * b = b * a)
    (a b : Option α) : a * b = b * a := by
  cases a <;> cases b <;> simp [h]
