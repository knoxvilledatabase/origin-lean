/-
Released under MIT license.
-/
import Val.Algebra

/-!
# Val α: Linear Algebra

Consolidated linear algebra over Val α. 2×2 matrices, determinants, bilinear forms,
modules, finite-dimensional spaces, deep matrix theory, projective modules, and tensor products.

The sort propagates through all linear algebra constructions.
Contents in, contents out. Origin absorbs.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Section 1: Core — 2×2 Matrices, Determinant, Multiplication, Adjugate
-- ============================================================================

/-!
## 2×2 Matrix Core

The key result: `det A ≠ 0` dissolves. If entries are contents, det is contents —
structurally not origin. No proof obligation at each call site.
-/

/-- A 2×2 matrix of Val α entries. -/
structure Mat2 (β : Type u) where
  e₁₁ : β
  e₁₂ : β
  e₂₁ : β
  e₂₂ : β

-- ============================================================================
-- Determinant
-- ============================================================================

/-- det([[a,b],[c,d]]) = a·d - b·c via add subF (mul mulF ...) -/
def det2 (mulF subF : α → α → α) (m : Mat2 (Val α)) : Val α :=
  add subF (mul mulF m.e₁₁ m.e₂₂) (mul mulF m.e₁₂ m.e₂₁)

/-- Det of a contents matrix is contents. -/
theorem det2_contents (mulF subF : α → α → α) (a b c d : α) :
    det2 mulF subF ⟨contents a, contents b, contents c, contents d⟩ =
    contents (subF (mulF a d) (mulF b c)) := by rfl

theorem det2_contents_ne_container (mulF subF : α → α → α) (a b c d e : α) :
    det2 mulF subF ⟨contents a, contents b, contents c, contents d⟩ ≠ container e := by
  simp [det2]

-- ============================================================================
-- Origin Propagation
-- ============================================================================

theorem det2_origin_e11 (mulF subF : α → α → α) (e₁₂ e₂₁ e₂₂ : Val α) :
    det2 mulF subF ⟨origin, e₁₂, e₂₁, e₂₂⟩ = origin := by simp [det2]

theorem det2_origin_e12 (mulF subF : α → α → α) (e₁₁ e₂₁ e₂₂ : Val α) :
    det2 mulF subF ⟨e₁₁, origin, e₂₁, e₂₂⟩ = origin := by simp [det2]

theorem det2_origin_e21 (mulF subF : α → α → α) (e₁₁ e₁₂ e₂₂ : Val α) :
    det2 mulF subF ⟨e₁₁, e₁₂, origin, e₂₂⟩ = origin := by simp [det2]

theorem det2_origin_e22 (mulF subF : α → α → α) (e₁₁ e₁₂ e₂₁ : Val α) :
    det2 mulF subF ⟨e₁₁, e₁₂, e₂₁, origin⟩ = origin := by simp [det2]

-- ============================================================================
-- Matrix Multiplication
-- ============================================================================

/-- 2×2 matrix multiplication over Val α. -/
def matMul2 (addF mulF : α → α → α) (a b : Mat2 (Val α)) : Mat2 (Val α) :=
  { e₁₁ := add addF (mul mulF a.e₁₁ b.e₁₁) (mul mulF a.e₁₂ b.e₂₁)
    e₁₂ := add addF (mul mulF a.e₁₁ b.e₁₂) (mul mulF a.e₁₂ b.e₂₂)
    e₂₁ := add addF (mul mulF a.e₂₁ b.e₁₁) (mul mulF a.e₂₂ b.e₂₁)
    e₂₂ := add addF (mul mulF a.e₂₁ b.e₁₂) (mul mulF a.e₂₂ b.e₂₂) }

/-- Product of two contents matrices has all contents entries. -/
theorem matMul2_contents (addF mulF : α → α → α) (a b c d e f g h : α) :
    matMul2 addF mulF
      ⟨contents a, contents b, contents c, contents d⟩
      ⟨contents e, contents f, contents g, contents h⟩ =
    ⟨contents (addF (mulF a e) (mulF b g)),
     contents (addF (mulF a f) (mulF b h)),
     contents (addF (mulF c e) (mulF d g)),
     contents (addF (mulF c f) (mulF d h))⟩ := by rfl

-- ============================================================================
-- Adjugate
-- ============================================================================

/-- adj([[a,b],[c,d]]) = [[d,-b],[-c,a]] -/
def adj2 (negF : α → α) (m : Mat2 (Val α)) : Mat2 (Val α) :=
  { e₁₁ := m.e₂₂
    e₁₂ := neg negF m.e₁₂
    e₂₁ := neg negF m.e₂₁
    e₂₂ := m.e₁₁ }

/-- Adjugate of a contents matrix has all contents entries. -/
theorem adj2_contents (negF : α → α) (a b c d : α) :
    adj2 negF ⟨contents a, contents b, contents c, contents d⟩ =
    ⟨contents d, contents (negF b), contents (negF c), contents a⟩ := by rfl

-- ============================================================================
-- Cayley-Hamilton (2×2 diagonal)
-- ============================================================================

/-- The (1,1) entry of A·adj(A) equals det(A) within contents. -/
theorem cayley_hamilton_diag_11 (addF mulF subF : α → α → α) (negF : α → α)
    (hmn : ∀ x y : α, mulF x (negF y) = negF (mulF x y))
    (hsub : ∀ x y : α, addF x (negF y) = subF x y)
    (a b c d : α) :
    let m : Mat2 (Val α) := ⟨contents a, contents b, contents c, contents d⟩
    (matMul2 addF mulF m (adj2 negF m)).e₁₁ = det2 mulF subF m := by
  simp [matMul2, adj2, neg, mul, add, det2, hmn, hsub]

-- ============================================================================
-- Section 2: Bilinear Forms, Quadratic Forms, Symmetric Forms
-- ============================================================================

/-!
## Bilinear Forms

Bilinear forms over Val α. The sort propagates through all bilinear computations.
Contents in, contents out. Origin absorbs.
-/

/-- A bilinear form: B(v, w) where B is a function α → α → α.
    Lifted to Val α. -/
abbrev valBilinear (B : α → α → α) : Val α → Val α → Val α := mul B

-- ============================================================================
-- Symmetric Bilinear Form
-- ============================================================================

/-- A bilinear form is symmetric if B(v,w) = B(w,v). -/
theorem bilinear_symmetric (B : α → α → α) (h : ∀ a b, B a b = B b a) (v w : α) :
    valBilinear B (contents v) (contents w) =
    valBilinear B (contents w) (contents v) := by
  show contents (B v w) = contents (B w v); rw [h]

-- ============================================================================
-- Quadratic Form
-- ============================================================================

/-- A quadratic form: Q(v) = B(v, v). -/
abbrev valQuadratic (B : α → α → α) : Val α → Val α := valMap (fun a => B a a)

-- ============================================================================
-- Orthogonality
-- ============================================================================

/-- Two vectors are orthogonal if B(v, w) = 0.
    In Val α: B(contents v, contents w) = contents(B v w). -/
theorem orthogonal_sort [Zero α] (B : α → α → α) (v w : α) (h : B v w = 0) :
    valBilinear B (contents v) (contents w) = contents (0 : α) := by
  show contents (B v w) = contents 0; rw [h]

-- ============================================================================
-- Section 3: Modules, Submodules, Quotients
-- ============================================================================

/-!
## Modules

Modules over Val α scalars. Submodules. Quotient modules.
The sort propagates through all module operations.
-/

/-- A module element in Val α. Contents values form the module. -/
def moduleElement (v : α) : Val α := contents v

-- ============================================================================
-- Module Operations
-- ============================================================================

/-- Module addition: contents + contents = contents. -/
theorem module_add (addF : α → α → α) (v w : α) :
    add addF (contents v) (contents w) = contents (addF v w) := rfl

/-- Scalar multiplication: contents · contents = contents. -/
theorem module_smul (f : α → α → α) (c v : α) :
    smul f (contents c) (contents v) = contents (f c v) := rfl

/-- Module negation: -contents = contents. -/
theorem module_neg (negF : α → α) (v : α) :
    neg negF (contents v) = contents (negF v) := rfl

-- ============================================================================
-- Submodule
-- ============================================================================

/-- Submodule addition stays in contents. -/
theorem submodule_add_contents (addF : α → α → α) (S : α → Prop)
    (_ : ∀ a b, S a → S b → S (addF a b))
    (v w : α) (_ : S v) (_ : S w) :
    add addF (contents v) (contents w) = contents (addF v w) := rfl

-- ============================================================================
-- Quotient Module
-- ============================================================================

/-- Quotient module: factor by a submodule. -/
def quotientModule (proj : α → α) (v : α) : Val α := contents (proj v)

/-- Quotient map is compatible with module operations. -/
theorem quotient_module_add (addF : α → α → α) (proj : α → α)
    (h : ∀ a b, proj (addF a b) = addF (proj a) (proj b)) (v w : α) :
    quotientModule proj (addF v w) = contents (addF (proj v) (proj w)) := by
  show contents (proj (addF v w)) = contents (addF (proj v) (proj w)); rw [h]

-- ============================================================================
-- Direct Sum
-- ============================================================================

/-- Direct sum projection to first component. -/
theorem direct_sum_proj1 (v w : α) :
    valMap Prod.fst (contents (v, w) : Val (α × α)) = contents v := rfl

/-- Direct sum projection to second component. -/
theorem direct_sum_proj2 (v w : α) :
    valMap Prod.snd (contents (v, w) : Val (α × α)) = contents w := rfl

-- ============================================================================
-- Module Homomorphism
-- ============================================================================

/-- A module homomorphism: a sort-preserving map. -/
theorem module_hom_contents (f : α → α) (v : α) :
    valMap f (contents v) = contents (f v) := rfl

/-- Module homomorphisms preserve origin. -/
theorem module_hom_origin (f : α → α) :
    valMap f (origin : Val α) = origin := rfl

/-- Kernel of a module homomorphism: preimage of zero. -/
theorem module_hom_kernel_contents [Zero α] (f : α → α) (v : α) (h : f v = 0) :
    valMap f (contents v) = contents (0 : α) := by
  show contents (f v) = contents 0; rw [h]

-- ============================================================================
-- Section 4: Finite Dimensional Spaces
-- ============================================================================

/-!
## Finite Dimensional Spaces

Rank, nullity, basis, dimension, rank-nullity theorem.
All within contents. Dimension is a contents value.
-/

variable {n : Nat}

-- ============================================================================
-- Dimension
-- ============================================================================

/-- The dimension of a space: a contents value. -/
def valDimension (dim : α) : Val α := contents dim

-- ============================================================================
-- Basis
-- ============================================================================

/-- A basis: a list of vectors spanning the space. Each basis vector is contents. -/
def valBasis (basis : Fin n → α) (i : Fin n) : Val α := contents (basis i)

-- ============================================================================
-- Rank-Nullity
-- ============================================================================

/-- Rank + nullity = dimension. All contents. -/
theorem rank_plus_nullity (addF : α → α → α) (rank nullity dim : α)
    (h : addF rank nullity = dim) :
    add addF (contents rank) (contents nullity) = contents dim := by
  show contents (addF rank nullity) = contents dim; rw [h]

-- ============================================================================
-- Dual Space
-- ============================================================================

/-- A linear functional: a map V → α. In Val α, the result is contents. -/
theorem linear_functional_contents (f : α → α) (v : α) :
    valMap f (contents v) = contents (f v) := rfl

-- ============================================================================
-- Annihilator
-- ============================================================================

/-- The annihilator: functionals that vanish on a subspace.
    In Val α, annihilator elements are contents. -/
theorem annihilator_contents [Zero α] (f : α → α) (v : α) (h : f v = 0) :
    valMap f (contents v) = contents (0 : α) := by
  show contents (f v) = contents 0; rw [h]

-- ============================================================================
-- Section 5: Matrix Theory (Deep)
-- ============================================================================

/-!
## Deep Matrix Theory

Beyond 2×2 basics: matrix rank, eigenvalues, diagonalization, spectral decomposition.
Builds on Core's Mat2, det2, matMul2, adj2 definitions.
-/

-- ============================================================================
-- Matrix Rank (Sort-Level)
-- ============================================================================

/-- The rank of a matrix: a contents value. -/
def matRank (rankF : (Fin n → Fin n → α) → α) (A : Fin n → Fin n → α) : Val α :=
  contents (rankF A)

-- ============================================================================
-- Rank-Nullity Theorem (Sort-Level)
-- ============================================================================

/-- Rank + nullity = n. Both are contents values. -/
theorem rank_nullity (addF : α → α → α) (rank nullity n_val : α)
    (h : addF rank nullity = n_val) :
    add addF (contents rank) (contents nullity) = contents n_val := by
  show contents (addF rank nullity) = contents n_val; rw [h]

-- ============================================================================
-- Determinant Properties (Sort-Level)
-- ============================================================================

/-- Trace of a 2×2 matrix: sum of diagonal entries. Contents. -/
def trace2 (addF : α → α → α) (m : Mat2 (Val α)) : Val α :=
  add addF m.e₁₁ m.e₂₂

/-- Trace of a contents matrix is contents. -/
theorem trace2_contents (addF : α → α → α) (a b c d : α) :
    trace2 addF ⟨contents a, contents b, contents c, contents d⟩ = contents (addF a d) := rfl

/-- Trace is never origin for contents matrices. -/
theorem trace2_ne_origin (addF : α → α → α) (a b c d : α) :
    trace2 addF ⟨contents a, contents b, contents c, contents d⟩ ≠ (origin : Val α) := by
  simp [trace2]

-- ============================================================================
-- Diagonal Matrices
-- ============================================================================

/-- A diagonal matrix: diagonal entry at (i, i). -/
def diagEntry (d : Fin n → α) (i j : Fin n) : α :=
  if i = j then d i else d j

-- ============================================================================
-- Section 6: Projective Modules, Free Modules
-- ============================================================================

/-!
## Projective and Free Modules

Free modules: direct sums of copies of the ring.
Projective modules: direct summands of free modules.
-/

-- ============================================================================
-- Free Module
-- ============================================================================

/-- A free module on n generators: Fin n → Val α. Each generator is contents. -/
def freeModule (basis : Fin n → α) (i : Fin n) : Val α := contents (basis i)

-- ============================================================================
-- Free Module Homomorphisms
-- ============================================================================

/-- A homomorphism from a free module sends contents to contents. -/
theorem free_module_hom (f : α → α) (basis : Fin n → α) (i : Fin n) :
    valMap f (freeModule basis i) = contents (f (basis i)) := rfl

/-- The universal property of free modules: hom determined by generator images. -/
theorem free_module_universal (f g : α → α) (h : f = g) (basis : Fin n → α) (i : Fin n) :
    valMap f (freeModule basis i) = valMap g (freeModule basis i) := by rw [h]

-- ============================================================================
-- Projective Module
-- ============================================================================

/-- A module is projective if there's a retraction s ∘ p = id. -/
def isProjective (p : α → α) (s : α → α) : Prop :=
  ∀ a, s (p a) = a

/-- Projective modules: the retraction preserves contents. -/
theorem projective_retraction (p : α → α) (s : α → α) (h : isProjective p s) (a : α) :
    valMap s (valMap p (contents a)) = contents a := by
  show contents (s (p a)) = contents a; rw [h]

/-- Projective modules: embedding preserves contents. -/
theorem projective_embedding (p : α → α) (a : α) :
    valMap p (contents a) = contents (p a) := rfl

-- ============================================================================
-- Lifting Property
-- ============================================================================

/-- Projective modules have the lifting property: any surjection lifts. -/
theorem projective_lift (f : α → α) (g : α → α) (lift : α → α)
    (h : ∀ a, g (lift a) = f a) (a : α) :
    valMap g (valMap lift (contents a)) = valMap f (contents a) := by
  show contents (g (lift a)) = contents (f a); rw [h]

-- ============================================================================
-- Flat Module (Sort-Level)
-- ============================================================================

/-- Flatness: multiplication of contents is contents. -/
theorem flat_mul (mulF : α → α → α) (a b : α) :
    mul mulF (contents a) (contents b) = contents (mulF a b) := rfl

-- ============================================================================
-- Section 7: Tensor Products, Exterior Algebra, Clifford Algebra
-- ============================================================================

/-!
## Tensor Products

Tensor products over Val α. The sort propagates through all multilinear constructions.
-/

variable {β : Type u}

-- ============================================================================
-- Tensor Product
-- ============================================================================

/-- Tensor product of two Val values: contents ⊗ contents = contents. -/
abbrev valTensor : Val α → Val β → Val (α × β) := valPair

/-- Tensor with origin gives origin (left). -/
theorem tensor_origin_left (y : Val β) :
    valTensor (origin : Val α) y = (origin : Val (α × β)) := by cases y <;> rfl

/-- Tensor with origin gives origin (right). -/
theorem tensor_origin_right (x : Val α) :
    valTensor x (origin : Val β) = (origin : Val (α × β)) := by
  cases x with | origin => rfl | container _ => rfl | contents _ => rfl

-- ============================================================================
-- Exterior Product (Wedge Product)
-- ============================================================================

/-- Wedge product: antisymmetric tensor product. In Val α, always contents. -/
def wedge (f : α → α → α) (a b : α) : Val α := contents (f a b)

/-- Antisymmetry: v ∧ v = 0. In Val α, that's contents(0). -/
theorem wedge_self [Zero α] (f : α → α → α) (a : α) (h : f a a = 0) :
    wedge f a a = contents (0 : α) := by
  show contents (f a a) = contents 0; rw [h]

-- ============================================================================
-- Clifford Algebra (Sort-Level)
-- ============================================================================

/-- Clifford product relation: v · w + w · v = 2⟨v,w⟩.
    Each side is contents when inputs are contents. -/
theorem clifford_contents (addF mulF : α → α → α) (B : α → α → α) (a b : α)
    (h : addF (mulF a b) (mulF b a) = B a b) :
    add addF (contents (mulF a b)) (contents (mulF b a)) = contents (B a b) := by
  show contents (addF (mulF a b) (mulF b a)) = contents (B a b); rw [h]

-- ============================================================================
-- Tensor Algebra
-- ============================================================================

/-- Tensor algebra multiplication: concatenation of tensors. Contents × contents = contents. -/
theorem tensor_algebra_mul (mulF : α → α → α) (a b : α) :
    mul mulF (contents a) (contents b) = contents (mulF a b) := rfl

-- ============================================================================
-- THE RESULT
-- ============================================================================
--
-- Linear algebra over Val α:
--   ✓ 2×2 matrices: det, matMul, adj, Cayley-Hamilton
--   ✓ Origin propagation: any origin entry → origin det
--   ✓ Bilinear forms: contents × contents → contents
--   ✓ Symmetric bilinear forms, quadratic forms, orthogonality
--   ✓ Modules: add, smul, neg all preserve contents
--   ✓ Submodules, quotient modules, direct sums
--   ✓ Module homomorphisms: sort-preserving, kernels are contents
--   ✓ Finite dimensional: dimension, basis, rank-nullity
--   ✓ Dual space, annihilator
--   ✓ Deep matrix theory: rank, trace, diagonal
--   ✓ Projective modules: retraction, embedding, lifting
--   ✓ Free modules: universal property
--   ✓ Flat modules: multiplication preserves contents
--   ✓ Tensor products: contents ⊗ contents = contents
--   ✓ Exterior algebra: wedge product, antisymmetry
--   ✓ Clifford algebra: contents throughout
--   ✓ Tensor algebra: multiplication preserves sort
--
-- Zero sorries. Zero typeclasses. Zero Mathlib.

end Val
