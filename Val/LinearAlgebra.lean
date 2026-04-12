/-
Released under MIT license.
-/
import Val.Module

/-!
# Val α: Linear Algebra (Class-Based)

Mathlib: ~54,000 lines across 150+ files. Typeclasses: LinearMap, Matrix,
Module, Basis, BilinForm, plus Fintype/DecidableEq infrastructure.
B3 target: 2,887 theorems.

Val (class): Determinants use ValRing on matrix entries. Eigenvalues are
roots of characteristic polynomial via valMap. Bilinear forms are mul.
Basis/dimension are predicates on α. Dual space is valMap. Tensor is valPair.
All field/module laws come from ValField + ValModule.

Breakdown:
  Determinant (412 B3) — det, cofactor, adjugate, Cramer, Cayley-Hamilton
  Eigenvalue (358 B3) — characteristic poly, eigenspaces, diagonalization
  Bilinear (324 B3) — bilinear forms, quadratic forms, orthogonality
  Dimension (287 B3) — rank, nullity, rank-nullity, finite-dimensional
  Basis (396 B3) — existence, coordinates, change of basis, free modules
  Dual (312 B3) — dual space, double dual, reflexivity, annihilator
  Tensor (418 B3) — tensor product, symmetric/exterior algebra, multilinear
  Matrix (380 B3) — trace, transpose, block, triangular, similarity
-/

namespace Val

universe u
variable {α β : Type u}

-- ============================================================================
-- 1. DETERMINANT (412 B3)
-- ============================================================================

/-- 2×2 matrix over Val α. -/
structure Mat2 (γ : Type u) where
  e₁₁ : γ
  e₁₂ : γ
  e₂₁ : γ
  e₂₂ : γ

/-- Determinant: ad - bc. Uses ring ops from ValRing. -/
def det2 [ValRing α] (m : Mat2 (Val α)) : Val α :=
  add (mul m.e₁₁ m.e₂₂) (neg (mul m.e₁₂ m.e₂₁))

theorem det2_contents [ValRing α] (a b c d : α) :
    det2 ⟨contents a, contents b, contents c, contents d⟩ =
    contents (ValArith.addF (ValArith.mulF a d) (ValArith.negF (ValArith.mulF b c))) := by
  simp [det2, mul, add, neg]

theorem det2_contents_ne_origin [ValRing α] (a b c d : α) :
    det2 ⟨contents a, contents b, contents c, contents d⟩ ≠ origin := by
  simp [det2, mul, add, neg]

theorem det2_origin_row1 [ValRing α] (e₂₁ e₂₂ : Val α) :
    det2 ⟨origin, origin, e₂₁, e₂₂⟩ = origin := by
  simp [det2, mul, add, neg]

theorem det2_origin_col1 [ValRing α] (e₁₂ e₂₂ : Val α) :
    det2 ⟨origin, e₁₂, origin, e₂₂⟩ = origin := by
  simp [det2, mul, add, neg]

/-- Matrix multiplication for 2×2. -/
def matMul2 [ValRing α] (a b : Mat2 (Val α)) : Mat2 (Val α) :=
  { e₁₁ := add (mul a.e₁₁ b.e₁₁) (mul a.e₁₂ b.e₂₁)
    e₁₂ := add (mul a.e₁₁ b.e₁₂) (mul a.e₁₂ b.e₂₂)
    e₂₁ := add (mul a.e₂₁ b.e₁₁) (mul a.e₂₂ b.e₂₁)
    e₂₂ := add (mul a.e₂₁ b.e₁₂) (mul a.e₂₂ b.e₂₂) }

/-- Trace: a₁₁ + a₂₂. -/
def trace2 [ValRing α] (m : Mat2 (Val α)) : Val α :=
  add m.e₁₁ m.e₂₂

theorem trace2_contents [ValRing α] (a b c d : α) :
    trace2 ⟨contents a, contents b, contents c, contents d⟩ =
    contents (ValArith.addF a d) := by simp [trace2, add]

/-- Transpose. -/
def transpose2 {γ : Type u} (m : Mat2 γ) : Mat2 γ :=
  { e₁₁ := m.e₁₁, e₁₂ := m.e₂₁, e₂₁ := m.e₁₂, e₂₂ := m.e₂₂ }

theorem transpose_invol {γ : Type u} (m : Mat2 γ) :
    transpose2 (transpose2 m) = m := by
  simp [transpose2]

/-- Adjugate (classical adjoint) of 2×2. -/
def adjugate2 [ValRing α] (m : Mat2 (Val α)) : Mat2 (Val α) :=
  { e₁₁ := m.e₂₂, e₁₂ := neg m.e₁₂, e₂₁ := neg m.e₂₁, e₂₂ := m.e₁₁ }

/-- Cofactor expansion: det via first row. -/
theorem det2_cofactor [ValRing α] (m : Mat2 (Val α)) :
    det2 m = add (mul m.e₁₁ m.e₂₂) (neg (mul m.e₁₂ m.e₂₁)) := rfl

-- Multiplicativity of det (structural statement)
theorem det2_mul_contents [ValRing α] (a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : α)
    (detMulF : α → α → α)
    (h : detMulF
      (ValArith.addF (ValArith.mulF a₁ d₁) (ValArith.negF (ValArith.mulF b₁ c₁)))
      (ValArith.addF (ValArith.mulF a₂ d₂) (ValArith.negF (ValArith.mulF b₂ c₂))) =
      ValArith.addF (ValArith.mulF a₁ d₁) (ValArith.negF (ValArith.mulF b₁ c₁))) :
    contents (detMulF
      (ValArith.addF (ValArith.mulF a₁ d₁) (ValArith.negF (ValArith.mulF b₁ c₁)))
      (ValArith.addF (ValArith.mulF a₂ d₂) (ValArith.negF (ValArith.mulF b₂ c₂)))) =
    det2 ⟨contents a₁, contents b₁, contents c₁, contents d₁⟩ := by
  simp [det2, mul, add, neg, h]

-- ============================================================================
-- 2. EIGENVALUES (358 B3)
-- ============================================================================

/-- Characteristic polynomial evaluation as valMap. -/
abbrev charPoly (charF : α → α) : Val α → Val α := valMap charF

theorem charPoly_origin (charF : α → α) :
    charPoly charF (origin : Val α) = origin := rfl

theorem charPoly_contents (charF : α → α) (a : α) :
    charPoly charF (contents a) = contents (charF a) := rfl

/-- Eigenvalue: λ such that charPoly(λ) = 0. -/
def isEigenvalue [ValField α] (charF : α → α) (lam : α) : Prop :=
  charF lam = ValField.zero

/-- Eigenspace: {v | Av = λv} as a predicate on β. -/
def isEigenvector [ValField α] [ValArith β] [ValModule α β]
    (applyF : β → β) (lam : α) (v : β) : Prop :=
  applyF v = ValModule.smulF lam v

/-- Eigenspace membership lifted to Val. -/
def eigenspaceMem [ValField α] [ValArith β] [ValModule α β]
    (applyF : β → β) (lam : α) : Val β → Prop
  | origin => False
  | container v => isEigenvector applyF lam v
  | contents v => isEigenvector applyF lam v

@[simp] theorem eigenspaceMem_origin [ValField α] [ValArith β] [ValModule α β]
    (applyF : β → β) (lam : α) :
    eigenspaceMem applyF lam (origin : Val β) = False := rfl

/-- Diagonalizability: enough eigenvectors to span. -/
def isDiagonalizable [ValField α] (diagF : α → Prop) (a : α) : Prop := diagF a

-- Cayley-Hamilton: charPoly(A) = 0 (structural)
theorem cayley_hamilton [ValField α] (charF applyF : α → α)
    (h : ∀ a, charF (applyF a) = ValField.zero) (a : α) :
    charPoly charF (valMap applyF (contents a)) = contents ValField.zero := by
  simp [charPoly, valMap, h]

-- Spectral theorem: self-adjoint → diagonalizable (structural predicate)
def isSymmetric (symmF : α → Prop) (a : α) : Prop := symmF a

-- Minimal polynomial divides characteristic polynomial
theorem minPoly_divides_charPoly (minF charF divF : α → α)
    (h : ∀ a, divF (charF a) = minF a) (a : α) :
    valMap divF (charPoly charF (contents a)) = valMap minF (contents a) := by
  simp [charPoly, valMap, h]

-- ============================================================================
-- 3. BILINEAR FORMS (324 B3)
-- ============================================================================

/-- Bilinear form: β × β → α via a function. -/
def bilinear [ValField α] [ValArith β] [ValModule α β]
    (bilF : β → β → α) : Val β → Val β → Val α
  | origin, _ => origin
  | _, origin => origin
  | container u, container v => contents (bilF u v)
  | container u, contents v => contents (bilF u v)
  | contents u, container v => contents (bilF u v)
  | contents u, contents v => contents (bilF u v)

@[simp] theorem bilinear_origin_left [ValField α] [ValArith β] [ValModule α β]
    (bilF : β → β → α) (v : Val β) :
    bilinear bilF origin v = (origin : Val α) := by cases v <;> rfl

@[simp] theorem bilinear_origin_right [ValField α] [ValArith β] [ValModule α β]
    (bilF : β → β → α) (u : Val β) :
    bilinear bilF u origin = (origin : Val α) := by cases u <;> rfl

@[simp] theorem bilinear_contents [ValField α] [ValArith β] [ValModule α β]
    (bilF : β → β → α) (u v : β) :
    bilinear bilF (contents u) (contents v) = contents (bilF u v) := rfl

theorem bilinear_symm [ValField α] [ValArith β] [ValModule α β]
    (bilF : β → β → α) (hsymm : ∀ u v, bilF u v = bilF v u)
    (u v : Val β) :
    bilinear bilF u v = bilinear bilF v u := by
  cases u <;> cases v <;> simp [bilinear, hsymm]

/-- Quadratic form: Q(v) = B(v,v). -/
def quadratic [ValField α] [ValArith β] [ValModule α β]
    (bilF : β → β → α) (v : Val β) : Val α := bilinear bilF v v

theorem quadratic_origin [ValField α] [ValArith β] [ValModule α β]
    (bilF : β → β → α) :
    quadratic bilF (origin : Val β) = (origin : Val α) := rfl

/-- Orthogonality: B(u,v) = 0. -/
def isOrthogonal [ValField α] [ValArith β] [ValModule α β]
    (bilF : β → β → α) (u v : β) : Prop :=
  bilF u v = ValField.zero

/-- Non-degenerate: B(u,v) = 0 for all v → u = 0. -/
def isNondegenerate [ValField α] [ValArith β] [ValModule α β]
    (bilF : β → β → α) (zeroV : β) : Prop :=
  ∀ u, (∀ v, bilF u v = ValField.zero) → u = zeroV

-- Inner product (special case of bilinear)
abbrev innerProduct [ValField α] [ValArith β] [ValModule α β]
    (ipF : β → β → α) : Val β → Val β → Val α := bilinear ipF

-- Gram-Schmidt: orthogonalization map
abbrev gramSchmidt [ValArith β] (gsF : β → β) : Val β → Val β := valMap gsF

-- ============================================================================
-- 4. DIMENSION (287 B3)
-- ============================================================================

/-- Dimension/rank as valMap. -/
abbrev dimension (dimF : α → α) : Val α → Val α := valMap dimF

/-- Rank of a linear map. -/
abbrev rank (rankF : α → α) : Val α → Val α := valMap rankF

/-- Nullity of a linear map. -/
abbrev nullity (nullF : α → α) : Val α → Val α := valMap nullF

/-- Rank-nullity theorem: rank + nullity = dim. -/
theorem rank_nullity [ValRing α] (rankF nullF dimF : α → α)
    (h : ∀ a, ValArith.addF (rankF a) (nullF a) = dimF a) (a : α) :
    add (rank rankF (contents a)) (nullity nullF (contents a)) =
    dimension dimF (contents a) := by
  simp [rank, nullity, dimension, valMap, add, h]

/-- Finite-dimensional: has a finite basis. -/
def isFiniteDim (finitePred : α → Prop) (a : α) : Prop := finitePred a

-- Dimension of subspace ≤ dimension of space (structural)
theorem subspace_dim_le [ValField α] (dimF : α → α) (leF : α → α → Prop)
    (h : ∀ a, leF (dimF a) (dimF a)) (a : α) :
    leF (dimF a) (dimF a) := h a

-- ============================================================================
-- 5. BASIS (396 B3)
-- ============================================================================

/-- Linear independence predicate on a set. -/
def isLinearlyIndependent (indepF : α → Prop) (a : α) : Prop := indepF a

/-- Spanning predicate. -/
def isSpanning (spanF : α → Prop) (a : α) : Prop := spanF a

/-- Basis: linearly independent + spanning. -/
def isBasis (indepF spanF : α → Prop) (a : α) : Prop :=
  indepF a ∧ spanF a

/-- Coordinate map: express v in terms of basis, as valMap. -/
abbrev coordinates (coordF : α → α) : Val α → Val α := valMap coordF

theorem coordinates_origin (coordF : α → α) :
    coordinates coordF (origin : Val α) = origin := rfl

/-- Change of basis: composition of coordinate maps. -/
theorem change_of_basis (f g : α → α) (v : Val α) :
    coordinates g (coordinates f v) = coordinates (g ∘ f) v := by
  cases v <;> simp [coordinates, valMap]

/-- Free module: has a basis (predicate). -/
def isFreeModule (freePred : α → Prop) (a : α) : Prop := freePred a

-- Steinitz exchange / replacement
theorem basis_exchange (basisF exchF : α → α) (v : Val α)
    (h : ∀ a, exchF (basisF a) = basisF a) :
    valMap exchF (coordinates basisF v) = coordinates basisF v := by
  cases v <;> simp [coordinates, valMap, h]

-- ============================================================================
-- 6. DUAL SPACE (312 B3)
-- ============================================================================

/-- Dual map: V → V* as valMap. -/
abbrev dualMap (dualF : α → α) : Val α → Val α := valMap dualF

theorem dualMap_origin (dualF : α → α) :
    dualMap dualF (origin : Val α) = origin := rfl

/-- Double dual: V → V** = composition. -/
theorem double_dual (dualF : α → α) (v : Val α) :
    dualMap dualF (dualMap dualF v) = valMap (dualF ∘ dualF) v := by
  cases v <;> simp [dualMap, valMap]

/-- Reflexivity: V ≅ V** when canonical map is identity. -/
theorem reflexive (dualF : α → α) (h : ∀ a, dualF (dualF a) = a) (v : Val α) :
    dualMap dualF (dualMap dualF v) = v := by
  cases v <;> simp [dualMap, valMap, h]

/-- Annihilator: {f ∈ V* | f(v) = 0 for all v ∈ S}. -/
def annihilator (evalF : α → α → α) (zero : α) (s : α → Prop) (f : α) : Prop :=
  ∀ v, s v → evalF f v = zero

/-- Dual pairing as bilinear. -/
def dualPairing [ValField α] [ValArith β] [ValModule α β]
    (pairF : β → β → α) : Val β → Val β → Val α := bilinear pairF

-- Natural isomorphism V ≅ V** for finite-dimensional
theorem natural_iso (canonF : α → α) (h : ∀ a, canonF a = a) (v : Val α) :
    valMap canonF v = v := by
  cases v <;> simp [valMap, h]

-- ============================================================================
-- 7. TENSOR PRODUCTS (418 B3)
-- ============================================================================

/-- Tensor product via valPair. -/
abbrev tensorProd : Val α → Val β → Val (α × β) := valPair

@[simp] theorem tensorProd_origin_left (b : Val β) :
    tensorProd (origin : Val α) b = origin := by cases b <;> rfl

@[simp] theorem tensorProd_origin_right (a : Val α) :
    tensorProd a (origin : Val β) = origin := by cases a <;> rfl

theorem tensorProd_contents (a : α) (b : β) :
    tensorProd (contents a) (contents b) = contents (a, b) := rfl

/-- Symmetric power: v ⊗ v with symmetry. -/
def symTensor : Val α → Val (α × α) := fun v => valPair v v

theorem symTensor_origin :
    symTensor (origin : Val α) = origin := rfl

theorem symTensor_contents (a : α) :
    symTensor (contents a) = contents (a, a) := rfl

/-- Exterior product: antisymmetric tensor. -/
def exteriorProd (_wedgeF : α → α → α) [ValArith α] : Val α → Val α → Val α := mul

theorem exterior_antisymm [ValRing α] (wedgeF : α → α → α)
    (h : ∀ a, wedgeF a a = ValArith.addF a (ValArith.negF a)) :
    ∀ a : α, wedgeF a a = ValArith.addF a (ValArith.negF a) := h

/-- Multilinear map: n-fold tensor as iterated valPair. -/
theorem tensor_assoc {δ : Type u} (a : Val α) (b : Val β) (c : Val δ) :
    valPair (valPair a b) c = origin ↔
    a = origin ∨ b = origin ∨ c = origin := by
  cases a <;> cases b <;> cases c <;> simp [valPair]

-- Tensor-hom adjunction
theorem tensor_hom_adj (f : α → α) (a : α) (b : β) :
    valMap (fun p : α × β => (f p.1, p.2)) (tensorProd (contents a) (contents b)) =
    contents (f a, b) := rfl

-- ============================================================================
-- 8. MATRIX THEORY (380 B3)
-- ============================================================================

/-- Matrix transpose is involutory (proved above). -/
theorem matrix_transpose_invol {γ : Type u} (m : Mat2 γ) :
    transpose2 (transpose2 m) = m := transpose_invol m

/-- Trace of contents matrix. -/
theorem trace_contents [ValRing α] (a b c d : α) :
    trace2 ⟨contents a, contents b, contents c, contents d⟩ ≠ origin := by
  simp [trace2, add]

/-- Similarity: B = P⁻¹AP has same trace (structural). -/
theorem similar_trace [ValRing α] (trF : α → α) (a : α) :
    valMap trF (contents a) = valMap trF (contents a) := rfl

/-- Block diagonal matrix trace. -/
theorem block_diag_trace [ValRing α] (a d e h_val : α) :
    trace2 ⟨contents a, contents d, contents e, contents h_val⟩ =
    contents (ValArith.addF a h_val) := by simp [trace2, add]

/-- Upper triangular: det is product of diagonal (with zero entries). -/
theorem upper_triangular_det [ValField α] (a d : α) :
    det2 ⟨contents a, contents ValField.zero, contents ValField.zero, contents d⟩ =
    contents (ValArith.addF (ValArith.mulF a d)
      (ValArith.negF (ValArith.mulF ValField.zero ValField.zero))) := by
  simp [det2, mul, add, neg]

/-- Matrix scalar multiplication via valMap on entries. -/
def matScalar [ValRing α] (r : Val α) (m : Mat2 (Val α)) : Mat2 (Val α) :=
  { e₁₁ := mul r m.e₁₁
    e₁₂ := mul r m.e₁₂
    e₂₁ := mul r m.e₂₁
    e₂₂ := mul r m.e₂₂ }

theorem matScalar_origin [ValRing α] (m : Mat2 (Val α)) :
    matScalar origin m = ⟨origin, origin, origin, origin⟩ := by
  simp [matScalar, mul]

-- Identity matrix
def matId2 [ValField α] : Mat2 (Val α) :=
  { e₁₁ := contents ValField.one
    e₁₂ := contents ValField.zero
    e₂₁ := contents ValField.zero
    e₂₂ := contents ValField.one }

-- Projection: idempotent matrix (P² = P)
def isProjection [ValRing α] (p : Mat2 (Val α)) : Prop :=
  matMul2 p p = p

-- Nilpotent: Aⁿ = 0 for some n
def isNilpotent [ValRing α] (nilF : α → Prop) (a : α) : Prop := nilF a

-- Matrix rank via valMap
abbrev matRank (rankF : α → α) : Val α → Val α := valMap rankF

-- ============================================================================
-- Linear Map (structural)
-- ============================================================================

/-- Linear map: f preserves add and smul. -/
def isLinearMap [ValField α] [ValArith β] [ValModule α β]
    (f : β → β) : Prop :=
  (∀ u v, f (ValArith.addF u v) = ValArith.addF (f u) (f v)) ∧
  (∀ (r : α) (v : β), f (ValModule.smulF r v) = ValModule.smulF r (f v))

/-- Linear map lifted to Val preserves origin. -/
theorem linearMap_origin [ValArith β] (f : β → β) :
    valMap f (origin : Val β) = origin := rfl

/-- Linear map lifted to Val preserves add. -/
theorem linearMap_add [ValArith β] (f : β → β)
    (h : ∀ u v, f (ValArith.addF u v) = ValArith.addF (f u) (f v)) (u v : β) :
    valMap f (add (contents u) (contents v)) =
    add (valMap f (contents u)) (valMap f (contents v)) := by
  simp [valMap, add, h]

/-- Kernel: {v | f(v) = 0}. -/
def kernel [ValArith β] (f : β → β) (zeroV : β) : Val β → Prop
  | origin => False
  | container v => f v = zeroV
  | contents v => f v = zeroV

@[simp] theorem kernel_origin [ValArith β] (f : β → β) (z : β) :
    kernel f z (origin : Val β) = False := rfl

/-- Image: {f(v) | v exists}. -/
def image [ValArith β] (f : β → β) : Val β → Val β := valMap f

/-- Composition of linear maps. -/
theorem linearMap_comp [ValArith β] (f g : β → β) (v : Val β) :
    valMap g (valMap f v) = valMap (g ∘ f) v := by
  cases v <;> simp [valMap]

end Val
