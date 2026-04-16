/-
Released under MIT license.
-/
import Origin.Core

/-!
# Model Theory on Option α (Core-based)

**Category 2** — pure math, no zero-management infrastructure.

Mathlib ModelTheory: 29 files, 10,204 lines, 976 genuine declarations.
This version keeps only domain-specific definitions and proofs that
actually use Option.

Model theory studies first-order languages, structures, theories,
and their models. Key concepts: languages (function and relation
symbols), structures (interpretations), homomorphisms, embeddings,
elementary equivalence, sentences, and theories.
-/

universe u
variable {α β : Type u}

-- ============================================================================
-- 1. LANGUAGES
-- ============================================================================

/-- A first-order language: function symbols and relation symbols by arity. -/
structure Language' where
  functions : Nat → Type u
  relations : Nat → Type u

/-- A language is relational if it has no function symbols. -/
def Language'.IsRelational (L : Language') : Prop :=
  ∀ n, (L.functions n → False)

/-- A language is algebraic if it has no relation symbols. -/
def Language'.IsAlgebraic (L : Language') : Prop :=
  ∀ n, (L.relations n → False)

/-- Constants are nullary function symbols. -/
abbrev Language'.Constants (L : Language') := L.functions 0

-- ============================================================================
-- 2. STRUCTURES
-- ============================================================================

/-- A structure interprets function and relation symbols over a type. -/
structure Structure' (L : Language') (M : Type u) where
  funMap : {n : Nat} → L.functions n → (Fin n → M) → M
  relMap : {n : Nat} → L.relations n → (Fin n → M) → Prop

-- ============================================================================
-- 3. HOMOMORPHISMS AND EMBEDDINGS
-- ============================================================================

/-- A homomorphism preserves function interpretations. -/
def IsHomomorphism (L : Language') (S₁ : Structure' L α) (S₂ : Structure' L β)
    (f : α → β) : Prop :=
  ∀ (n : Nat) (func : L.functions n) (args : Fin n → α),
    f (S₁.funMap func args) = S₂.funMap func (f ∘ args)

/-- An embedding is an injective homomorphism that preserves relations. -/
def IsEmbedding' (L : Language') (S₁ : Structure' L α) (S₂ : Structure' L β)
    (f : α → β) : Prop :=
  IsHomomorphism L S₁ S₂ f ∧ (∀ a b, f a = f b → a = b) ∧
  ∀ (n : Nat) (rel : L.relations n) (args : Fin n → α),
    S₁.relMap rel args ↔ S₂.relMap rel (f ∘ args)

-- ============================================================================
-- 4. THEORIES AND MODELS
-- ============================================================================

/-- A theory is a set of sentences (abstractly, propositions over a structure). -/
def Theory' (L : Language') (α : Type u) := (Structure' L α → Prop) → Prop

/-- A structure models a sentence. -/
def Models (L : Language') (sentence : Structure' L α → Prop) (S : Structure' L α) : Prop :=
  sentence S

-- ============================================================================
-- 5. ELEMENTARY EQUIVALENCE
-- ============================================================================

/-- Two structures are elementarily equivalent if they satisfy the same sentences. -/
def IsElementarilyEquivalent (L : Language')
    (S₁ : Structure' L α) (S₂ : Structure' L β)
    (transfer : (Structure' L α → Prop) → (Structure' L β → Prop)) : Prop :=
  ∀ φ, φ S₁ ↔ transfer φ S₂

-- ============================================================================
-- DEMONSTRATION: a domain law lifts through Option
-- ============================================================================

theorem model_mul_assoc [Mul α]
    (h : ∀ a b c : α, a * b * c = a * (b * c))
    (a b c : Option α) : a * b * c = a * (b * c) := by
  cases a <;> cases b <;> cases c <;> simp [h]

-- None absorbs (mul, neg, map): Core.lean's @[simp] set handles all cases.
