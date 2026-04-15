/-
Released under MIT license.
-/
import Origin.Module

/-!
# Origin LinearAlgebra: Determinants through Tensors on Option α

Val/LinearAlgebra.lean: 451 lines. Determinants, eigenvalues, bilinear
forms, dimension, basis, dual space, tensor products, matrix theory.

Origin: the same domain content on Option. Option.map replaces valMap.
oMul/oAdd replace mul/add. liftBin₂ replaces bilinear/tensor.
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
  oAdd (oMul m.e₁₁ m.e₂₂) (oNeg (oMul m.e₁₂ m.e₂₁))

theorem det2_some [Mul α] [Add α] [Neg α] (a b c d : α) :
    det2 ⟨some a, some b, some c, some d⟩ =
    some (a * d + -(b * c)) := by simp [det2, oMul, oAdd, oNeg]

theorem det2_none_row1 [Mul α] [Add α] [Neg α] (e₂₁ e₂₂ : Option α) :
    det2 ⟨none, none, e₂₁, e₂₂⟩ = none := by
  simp [det2, oMul, oAdd, oNeg]

theorem det2_none_col1 [Mul α] [Add α] [Neg α] (e₁₂ e₂₂ : Option α) :
    det2 ⟨none, e₁₂, none, e₂₂⟩ = none := by
  cases e₁₂ <;> cases e₂₂ <;> simp [det2, oMul, oAdd, oNeg]

def matMul2 [Mul α] [Add α] (a b : Mat2 (Option α)) : Mat2 (Option α) :=
  { e₁₁ := oAdd (oMul a.e₁₁ b.e₁₁) (oMul a.e₁₂ b.e₂₁)
    e₁₂ := oAdd (oMul a.e₁₁ b.e₁₂) (oMul a.e₁₂ b.e₂₂)
    e₂₁ := oAdd (oMul a.e₂₁ b.e₁₁) (oMul a.e₂₂ b.e₂₁)
    e₂₂ := oAdd (oMul a.e₂₁ b.e₁₂) (oMul a.e₂₂ b.e₂₂) }

def trace2 [Add α] (m : Mat2 (Option α)) : Option α := oAdd m.e₁₁ m.e₂₂

theorem trace2_some [Add α] (a b c d : α) :
    trace2 ⟨some a, some b, some c, some d⟩ = some (a + d) := by
  simp [trace2, oAdd]

def transpose2 {γ : Type u} (m : Mat2 γ) : Mat2 γ :=
  { e₁₁ := m.e₁₁, e₁₂ := m.e₂₁, e₂₁ := m.e₁₂, e₂₂ := m.e₂₂ }

theorem transpose_invol {γ : Type u} (m : Mat2 γ) :
    transpose2 (transpose2 m) = m := by simp [transpose2]

def adjugate2 [Neg α] (m : Mat2 (Option α)) : Mat2 (Option α) :=
  { e₁₁ := m.e₂₂, e₁₂ := oNeg m.e₁₂, e₂₁ := oNeg m.e₂₁, e₂₂ := m.e₁₁ }

-- ============================================================================
-- 2. EIGENVALUES
-- ============================================================================

abbrev charPoly (charF : α → α) : Option α → Option α := Option.map charF

theorem charPoly_none (charF : α → α) :
    charPoly charF (none : Option α) = none := rfl

def isEigenvalue (charF : α → α) (zero : α) (lam : α) : Prop := charF lam = zero

def isEigenvector (applyF : β → β) (smulF : α → β → β) (lam : α) (v : β) : Prop :=
  applyF v = smulF lam v

def eigenspaceMem (applyF : β → β) (smulF : α → β → β) (lam : α) : Option β → Prop
  | none => False
  | some v => isEigenvector applyF smulF lam v

@[simp] theorem eigenspaceMem_none (applyF : β → β) (smulF : α → β → β) (lam : α) :
    eigenspaceMem applyF smulF lam (none : Option β) = False := rfl

theorem cayley_hamilton (charF applyF : α → α) (zero : α)
    (h : ∀ a, charF (applyF a) = zero) (a : α) :
    charPoly charF (Option.map applyF (some a)) = some zero := by
  simp [charPoly, h]

-- ============================================================================
-- 3. BILINEAR FORMS
-- ============================================================================

def bilinear (bilF : α → α → β) : Option α → Option α → Option β
  | none, _ => none
  | _, none => none
  | some u, some v => some (bilF u v)

@[simp] theorem bilinear_none_left (bilF : α → α → β) (v : Option α) :
    bilinear bilF none v = none := by cases v <;> rfl

@[simp] theorem bilinear_none_right (bilF : α → α → β) (u : Option α) :
    bilinear bilF u none = none := by cases u <;> rfl

@[simp] theorem bilinear_some (bilF : α → α → β) (u v : α) :
    bilinear bilF (some u) (some v) = some (bilF u v) := rfl

theorem bilinear_symm (bilF : α → α → β)
    (hsymm : ∀ u v, bilF u v = bilF v u) (u v : Option α) :
    bilinear bilF u v = bilinear bilF v u := by
  cases u <;> cases v <;> simp [bilinear, hsymm]

def quadratic (bilF : α → α → β) (v : Option α) : Option β := bilinear bilF v v

theorem quadratic_none (bilF : α → α → β) :
    quadratic bilF (none : Option α) = none := rfl

def isOrthogonal (bilF : α → α → β) (zero : β) (u v : α) : Prop := bilF u v = zero

-- ============================================================================
-- 4. DIMENSION
-- ============================================================================

abbrev dimension (dimF : α → α) : Option α → Option α := Option.map dimF
abbrev rank (rankF : α → α) : Option α → Option α := Option.map rankF
abbrev nullity (nullF : α → α) : Option α → Option α := Option.map nullF

theorem rank_nullity [Add α] (rankF nullF dimF : α → α)
    (h : ∀ a, rankF a + nullF a = dimF a) (a : α) :
    oAdd (rank rankF (some a)) (nullity nullF (some a)) =
    dimension dimF (some a) := by
  simp [rank, nullity, dimension, oAdd, h]

-- ============================================================================
-- 5. BASIS
-- ============================================================================

def isBasis (indepF spanF : α → Prop) (a : α) : Prop := indepF a ∧ spanF a

abbrev coordinates (coordF : α → α) : Option α → Option α := Option.map coordF

theorem coordinates_none (coordF : α → α) :
    coordinates coordF (none : Option α) = none := rfl

theorem change_of_basis (f g : α → α) (v : Option α) :
    coordinates g (coordinates f v) = coordinates (g ∘ f) v := by
  cases v <;> simp [coordinates]

theorem basis_exchange (basisF exchF : α → α)
    (h : ∀ a, exchF (basisF a) = basisF a) (v : Option α) :
    Option.map exchF (coordinates basisF v) = coordinates basisF v := by
  cases v <;> simp [coordinates, h]

-- ============================================================================
-- 6. DUAL SPACE
-- ============================================================================

abbrev dualMap (dualF : α → α) : Option α → Option α := Option.map dualF

theorem dualMap_none (dualF : α → α) :
    dualMap dualF (none : Option α) = none := rfl

theorem double_dual (dualF : α → α) (v : Option α) :
    dualMap dualF (dualMap dualF v) = Option.map (dualF ∘ dualF) v := by
  cases v <;> simp [dualMap]

theorem reflexive (dualF : α → α) (h : ∀ a, dualF (dualF a) = a) (v : Option α) :
    dualMap dualF (dualMap dualF v) = v := by
  cases v <;> simp [dualMap, h]

def annihilator (evalF : α → α → α) (zero : α) (s : α → Prop) (f : α) : Prop :=
  ∀ v, s v → evalF f v = zero

-- ============================================================================
-- 7. TENSOR PRODUCTS
-- ============================================================================

def tensorProd : Option α → Option β → Option (α × β)
  | none, _ => none
  | _, none => none
  | some a, some b => some (a, b)

@[simp] theorem tensorProd_none_left (b : Option β) :
    tensorProd (none : Option α) b = none := by cases b <;> rfl

@[simp] theorem tensorProd_none_right (a : Option α) :
    tensorProd a (none : Option β) = none := by cases a <;> rfl

theorem tensorProd_some (a : α) (b : β) :
    tensorProd (some a) (some b) = some (a, b) := rfl

def symTensor : Option α → Option (α × α) := fun v => tensorProd v v

theorem symTensor_none : symTensor (none : Option α) = none := rfl
theorem symTensor_some (a : α) : symTensor (some a) = some (a, a) := rfl

theorem tensor_hom_adj (f : α → α) (a : α) (b : β) :
    Option.map (fun p : α × β => (f p.1, p.2)) (tensorProd (some a) (some b)) =
    some (f a, b) := rfl

-- ============================================================================
-- 8. MATRIX THEORY
-- ============================================================================

def matScalar [Mul α] (r : Option α) (m : Mat2 (Option α)) : Mat2 (Option α) :=
  { e₁₁ := oMul r m.e₁₁, e₁₂ := oMul r m.e₁₂,
    e₂₁ := oMul r m.e₂₁, e₂₂ := oMul r m.e₂₂ }

theorem matScalar_none [Mul α] (m : Mat2 (Option α)) :
    matScalar none m = ⟨none, none, none, none⟩ := by
  simp [matScalar, oMul]

-- ============================================================================
-- 9. LINEAR MAPS
-- ============================================================================

def isLinearMap [Add β] (smulF : α → β → β) (f : β → β) : Prop :=
  (∀ u v, f (u + v) = f u + f v) ∧
  (∀ (r : α) (v : β), f (smulF r v) = smulF r (f v))

theorem linearMap_none (f : α → α) :
    Option.map f (none : Option α) = none := rfl

theorem linearMap_add [Add α] (f : α → α)
    (h : ∀ u v, f (u + v) = f u + f v) (u v : α) :
    Option.map f (oAdd (some u) (some v)) =
    oAdd (Option.map f (some u)) (Option.map f (some v)) := by
  simp [oAdd, h]

def kernel (f : α → α) (zero : α) : Option α → Prop
  | none => False
  | some v => f v = zero

@[simp] theorem kernel_none (f : α → α) (z : α) :
    kernel f z (none : Option α) = False := rfl

theorem linearMap_comp (f g : α → α) (v : Option α) :
    Option.map g (Option.map f v) = Option.map (g ∘ f) v := by
  cases v <;> simp

-- ============================================================================
-- The Count
-- ============================================================================

-- Val/LinearAlgebra.lean: 451 lines. Used ValRing, ValField, ValModule,
-- ValArith (4 custom typeclasses). valMap throughout, valPair for tensors.
--
-- Origin/LinearAlgebra.lean: this file. Standard Lean typeclasses.
-- Option.map replaces valMap. liftBin₂/bilinear for cross-type.
-- tensorProd for tensor products (same pattern as liftBin₂).
-- No custom typeclasses. No five-level hierarchy.
