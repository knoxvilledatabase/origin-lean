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
-- 1. FIELD EXTENSION
-- ============================================================================

theorem fieldEmbed_comp (iota₁ iota₂ : α → α) (v : Option α) :
    Option.map iota₂ (Option.map iota₁ v) = Option.map (iota₂ ∘ iota₁) v := by
  cases v <;> simp

-- ============================================================================
-- 2. GALOIS THEORY
-- ============================================================================

theorem galois_fixes_base (sigma iota : α → α)
    (h : ∀ a, sigma (iota a) = iota a) (a : α) :
    Option.map sigma (Option.map iota (some a)) = Option.map iota (some a) := by
  simp [h]

theorem galois_comp (sigma tau : α → α) (v : Option α) :
    Option.map sigma (Option.map tau v) = Option.map (sigma ∘ tau) v := by
  cases v <;> simp

theorem galois_inv (sigma invS : α → α)
    (h : ∀ a, sigma (invS a) = a) (a : α) :
    Option.map sigma (Option.map invS (some a)) = some a := by simp [h]

theorem galois_id (v : Option α) : Option.map id v = v := by
  cases v <;> simp

-- ============================================================================
-- 3. GALOIS CORRESPONDENCE
-- ============================================================================

theorem galois_corr_left (fixF unfixF : α → α)
    (h : ∀ a, fixF (unfixF a) = a) (a : α) :
    Option.map fixF (Option.map unfixF (some a)) = some a := by simp [h]

theorem galois_corr_right (fixF unfixF : α → α)
    (h : ∀ a, unfixF (fixF a) = a) (a : α) :
    Option.map unfixF (Option.map fixF (some a)) = some a := by simp [h]

-- ============================================================================
-- 4. INTERMEDIATE FIELDS
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

theorem frobenius_comp (frobF : α → α) (v : Option α) :
    Option.map frobF (Option.map frobF v) = Option.map (frobF ∘ frobF) v := by
  cases v <;> simp

theorem perfect_frob_bij (frobF invFrob : α → α)
    (h₁ : ∀ a, frobF (invFrob a) = a) (h₂ : ∀ a, invFrob (frobF a) = a)
    (v : Option α) :
    Option.map frobF (Option.map invFrob v) = v ∧
    Option.map invFrob (Option.map frobF v) = v := by
  constructor <;> (cases v <;> simp [h₁, h₂])
