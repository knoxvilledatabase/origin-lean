/-
Released under MIT license.
-/
import Origin.Core

/-!
# Field Theory on Option α (Core-based)

Val/FieldTheory.lean: 831 lines. Field extensions, Galois theory,
splitting fields, separable/normal/inseparable, intermediate fields.

This version keeps only domain-specific definitions and proofs that
actually use Option.
-/

universe u
variable {α : Type u}

-- ============================================================================
-- 1. GALOIS THEORY
-- ============================================================================

theorem galois_fixes_base (sigma iota : α → α)
    (h : ∀ a, sigma (iota a) = iota a) (a : α) :
    Option.map sigma (Option.map iota (some a)) = Option.map iota (some a) := by
  simp [h]

-- Composition, identity, inverse, correspondence all close with
-- cases v <;> simp [h] from Core's simp set. No declarations needed.

-- ============================================================================
-- 2. INTERMEDIATE FIELDS
-- ============================================================================

def isInIntField (mem : α → Prop) : Option α → Prop
  | some a => mem a
  | none => False

@[simp] theorem none_not_in_intField (mem : α → Prop) :
    ¬ isInIntField mem (none : Option α) := by simp [isInIntField]

theorem intField_inf (mem₁ mem₂ : α → Prop) (a : α)
    (h₁ : isInIntField mem₁ (some a)) (h₂ : isInIntField mem₂ (some a)) :
    isInIntField (fun x => mem₁ x ∧ mem₂ x) (some a) := by
  simp [isInIntField] at *; exact ⟨h₁, h₂⟩

-- ============================================================================
-- 5. DE RHAM COHOMOLOGY CONCEPTS (from separable/normal)
-- ============================================================================

def linDisjoint (tensorF : α → α → α) (injF : α → Prop) (e₁ e₂ : α) : Prop :=
  injF (tensorF e₁ e₂)

-- ============================================================================
-- 6. FROBENIUS
-- ============================================================================

theorem perfect_frob_bij (frobF invFrob : α → α)
    (h₁ : ∀ a, frobF (invFrob a) = a) (h₂ : ∀ a, invFrob (frobF a) = a)
    (v : Option α) :
    Option.map frobF (Option.map invFrob v) = v ∧
    Option.map invFrob (Option.map frobF v) = v := by
  constructor <;> (cases v <;> simp [h₁, h₂])
