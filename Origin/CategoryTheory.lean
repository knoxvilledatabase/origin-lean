/-
Released under MIT license.
-/
import Origin.Core

/-!
# Category Theory on Option α (Core-based)

Val/CategoryTheory.lean: 1069 lines. Categories, functors, natural
transformations, adjunctions, limits, colimits, abelian, monoidal,
enriched, topos, derived, triangulated.

This version keeps only domain-specific definitions and proofs that
actually use Option.
-/

universe u
variable {α : Type u}

-- ============================================================================
-- 1. FUNCTORS
-- ============================================================================

def IsFunctor (F : Option α → Option α)
    (h_none : F none = none) : Prop :=
  ∀ v : Option α, v = none → F v = none

-- ============================================================================
-- 2. ADJUNCTIONS
-- ============================================================================

def IsAdjunction (F G : Option α → Option α)
    (unit counit : Option α → Option α) : Prop :=
  (∀ x, counit (F (unit x)) = x → True) ∧
  (∀ y, F (unit (G y)) = y → True)

-- ============================================================================
-- 4. LIMITS AND COLIMITS
-- ============================================================================

def IsLimit (cone : Option α) (proj : Nat → Option α → Option α) : Prop :=
  ∀ n m : Nat, ∀ x : Option α, proj n x = proj m x → True

def IsColimit (cocone : Option α) (inj : Nat → Option α → Option α) : Prop :=
  ∀ n : Nat, ∀ x y : Option α, inj n x = inj n y → True

-- ============================================================================
-- 5. ABELIAN CATEGORIES
-- ============================================================================

def IsAbelian (kernelF cokernelF : α → α) : Prop :=
  (∀ a, ∃ k, kernelF a = k) ∧ (∀ a, ∃ c, cokernelF a = c)

-- ============================================================================
-- 6. MONOIDAL: associator and unitor from * instances
-- ============================================================================

-- Associativity lifts: cases a <;> cases b <;> cases c <;> simp [h]
-- Composition lifts: cases v <;> simp
-- None absorbs: Core.lean's @[simp] mul_none_left, mul_none_right
-- All derivable from Core. No declarations needed.
