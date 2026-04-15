/-
Released under MIT license.
-/
import Origin.Core

/-!
# Group Theory on Option α (Core-based)

Val/GroupTheory.lean: 1140 lines. Groups, subgroups, homomorphisms,
quotients, Sylow, solvable, nilpotent, abelian, free groups,
semidirect products, group actions, transfer, Burnside.

This version keeps only domain-specific definitions and proofs that
actually use Option.
-/

universe u
variable {α : Type u}

-- ============================================================================
-- 1. GROUP STRUCTURE
-- ============================================================================

structure GroupAxioms (α : Type u) [Mul α] [Neg α] where
  assoc : ∀ a b c : α, a * b * c = a * (b * c)
  identity : α
  left_id : ∀ a : α, identity * a = a
  left_inv : ∀ a : α, (-a) * a = identity

-- ============================================================================
-- 2. SUBGROUPS
-- ============================================================================

def isSubgroup [Mul α] [Neg α] (mem : α → Prop) (e : α) : Prop :=
  mem e ∧ (∀ a b, mem a → mem b → mem (a * b)) ∧ (∀ a, mem a → mem (-a))

def isNormal [Mul α] [Neg α] (mem : α → Prop) : Prop :=
  ∀ g a, mem a → mem (g * a * -g)

-- ============================================================================
-- 3. HOMOMORPHISMS
-- ============================================================================

theorem hom_comp (f g : α → α) (v : Option α) :
    Option.map f (Option.map g v) = Option.map (f ∘ g) v := by
  cases v <;> simp

theorem hom_preserves_mul [Mul α] (f : α → α)
    (h : ∀ a b, f (a * b) = f a * f b) (a b : α) :
    Option.map f (some a * some b) = Option.map f (some a) * Option.map f (some b) := by
  simp [h]

-- ============================================================================
-- 4. QUOTIENT GROUPS
-- ============================================================================

def cosetEquiv [Mul α] [Neg α] (mem : α → Prop) (a b : α) : Prop :=
  mem (-a * b)

-- ============================================================================
-- 5. SYLOW THEOREMS
-- ============================================================================

def isSylowSubgroup (orderF : α → Nat) (p : Nat) (groupOrder : Nat) : α → Prop :=
  fun H => ∃ k, orderF H = p ^ k ∧ ¬(p ∣ groupOrder / p ^ k)

-- ============================================================================
-- 6. SOLVABLE AND NILPOTENT
-- ============================================================================

def isSolvable (derivedF : Nat → α → Prop) (trivial : α → Prop) : Prop :=
  ∃ n, ∀ a, derivedF n a → trivial a

def isNilpotent (lowerCentralF : Nat → α → Prop) (trivial : α → Prop) : Prop :=
  ∃ n, ∀ a, lowerCentralF n a → trivial a

-- ============================================================================
-- 7. ABELIAN GROUPS
-- ============================================================================

def isAbelian [Mul α] : Prop := ∀ a b : α, a * b = b * a

-- ============================================================================
-- 8. FREE GROUPS
-- ============================================================================

def IsFreeGroup (embed : α → α) (extend : (α → α) → α → α) : Prop :=
  ∀ f a, extend f (embed a) = f a

-- ============================================================================
-- 9. GROUP ACTIONS
-- ============================================================================

def isGroupAction [Mul α] (act : α → α → α) (e : α) : Prop :=
  (∀ x, act e x = x) ∧ (∀ g h x, act g (act h x) = act (g * h) x)

-- ============================================================================
-- 10. CONJUGACY
-- ============================================================================

def isConjugate [Mul α] [Neg α] (a b : α) : Prop :=
  ∃ g, g * a * -g = b

-- ============================================================================
-- 11. NONE ABSORBS
-- ============================================================================

theorem group_none_mul [Mul α] (b : Option α) :
    (none : Option α) * b = none := by simp

theorem group_mul_none [Mul α] (a : Option α) :
    a * (none : Option α) = none := by simp

theorem group_some_mul [Mul α] (a b : α) :
    (some a : Option α) * some b = some (a * b) := by simp

theorem group_neg_none [Neg α] :
    -(none : Option α) = none := by simp

theorem group_neg_some [Neg α] (a : α) :
    -(some a : Option α) = some (-a) := by simp
