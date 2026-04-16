/-
Released under MIT license.
-/
import Origin.Core

/-!
# Linear Algebra on Option α (Core-based)

Val/LinearAlgebra.lean: 451 lines. Determinants, eigenvalues, bilinear forms,
dimension, basis, dual space, tensor products, matrix theory.

This version keeps only domain-specific definitions and proofs that
actually use Option.
-/

universe u
variable {α β : Type u}

-- ============================================================================
-- 1. DETERMINANT
-- ============================================================================

structure Mat2 (γ : Type u) where
  e₁₁ : γ
  e₁₂ : γ
  e₂₁ : γ
  e₂₂ : γ

def det2 [Mul α] [Add α] [Neg α] (m : Mat2 (Option α)) : Option α :=
  m.e₁₁ * m.e₂₂ + -(m.e₁₂ * m.e₂₁)

theorem det2_some [Mul α] [Add α] [Neg α] (a b c d : α) :
    det2 ⟨some a, some b, some c, some d⟩ =
    some (a * d + -(b * c)) := by simp [det2]

theorem det2_none_row [Mul α] [Add α] [Neg α] (e₂₁ e₂₂ : Option α) :
    det2 ⟨none, none, e₂₁, e₂₂⟩ = none := by
  simp [det2]

def trace2 [Add α] (m : Mat2 (Option α)) : Option α := m.e₁₁ + m.e₂₂

theorem trace2_some [Add α] (a b c d : α) :
    trace2 ⟨some a, some b, some c, some d⟩ = some (a + d) := by
  simp [trace2]

def transpose2 {γ : Type u} (m : Mat2 γ) : Mat2 γ :=
  { e₁₁ := m.e₁₁, e₁₂ := m.e₂₁, e₂₁ := m.e₁₂, e₂₂ := m.e₂₂ }

theorem transpose_invol {γ : Type u} (m : Mat2 γ) :
    transpose2 (transpose2 m) = m := by simp [transpose2]

-- ============================================================================
-- 2. EIGENVALUES
-- ============================================================================

def isEigenvalue (charF : α → α) (zero : α) (lam : α) : Prop := charF lam = zero

-- ============================================================================
-- 3. BILINEAR FORMS
-- ============================================================================

def bilinear (bilF : α → α → α) : Option α → Option α → Option α
  | some u, some v => some (bilF u v)
  | _, _ => none

@[simp] theorem bilinear_none_left (bilF : α → α → α) (v : Option α) :
    bilinear bilF none v = none := by cases v <;> rfl

@[simp] theorem bilinear_none_right (bilF : α → α → α) (u : Option α) :
    bilinear bilF u none = none := by cases u <;> rfl

@[simp] theorem bilinear_some (bilF : α → α → α) (u v : α) :
    bilinear bilF (some u) (some v) = some (bilF u v) := rfl

theorem bilinear_symm (bilF : α → α → α) (hsymm : ∀ u v, bilF u v = bilF v u)
    (u v : Option α) : bilinear bilF u v = bilinear bilF v u := by
  cases u <;> cases v <;> simp [bilinear, hsymm]

def isOrthogonal (bilF : α → α → α) (zero : α) (u v : α) : Prop := bilF u v = zero

-- ============================================================================
-- 4. DIMENSION
-- ============================================================================

def isBasis (indepF spanF : α → Prop) (a : α) : Prop := indepF a ∧ spanF a

-- ============================================================================
-- 5. DUAL SPACE
-- ============================================================================

-- double_dual, reflexive: composition/involution patterns, derivable from Core.

-- ============================================================================
-- 6. TENSOR PRODUCTS
-- ============================================================================

def tensorProd : Option α → Option β → Option (α × β)
  | some a, some b => some (a, b)
  | _, _ => none

@[simp] theorem tensorProd_none_left (b : Option β) :
    tensorProd (none : Option α) b = none := by cases b <;> rfl

@[simp] theorem tensorProd_none_right (a : Option α) :
    tensorProd a (none : Option β) = none := by cases a <;> rfl

theorem tensorProd_some (a : α) (b : β) :
    tensorProd (some a) (some b) = some (a, b) := rfl

-- ============================================================================
-- 7. LINEAR MAP
-- ============================================================================

-- linearMap_comp: composition pattern, derivable from Core.
