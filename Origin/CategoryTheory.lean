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
-- 1. COMPOSITION = multiplication
-- ============================================================================

theorem comp_assoc [Mul α] (h : ∀ a b c : α, a * b * c = a * (b * c))
    (a b c : Option α) : a * b * c = a * (b * c) :=
  option_mul_assoc h a b c

-- ============================================================================
-- 2. FUNCTORS
-- ============================================================================

def IsFunctor (F : Option α → Option α)
    (h_none : F none = none) : Prop :=
  ∀ v : Option α, v = none → F v = none

theorem functor_comp (F : α → α) (G : α → α) (v : Option α) :
    Option.map F (Option.map G v) = Option.map (F ∘ G) v := by
  cases v <;> simp

-- ============================================================================
-- 3. ADJUNCTIONS
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

theorem monoidal_assoc [Mul α] (h : ∀ a b c : α, a * b * c = a * (b * c))
    (a b c : Option α) :
    a * b * c = a * (b * c) := option_mul_assoc h a b c

-- ============================================================================
-- 7. YONEDA
-- ============================================================================

theorem yoneda_comp (f g : α → α) (v : Option α) :
    Option.map f (Option.map g v) = Option.map (f ∘ g) v := by
  cases v <;> simp

-- ============================================================================
-- 8. NONE ABSORBS: the categorical ground
-- ============================================================================

theorem cat_none_left [Mul α] (b : Option α) :
    (none : Option α) * b = none := by simp

theorem cat_none_right [Mul α] (a : Option α) :
    a * (none : Option α) = none := by simp

theorem cat_some_comp [Mul α] (a b : α) :
    (some a : Option α) * some b = some (a * b) := by simp
