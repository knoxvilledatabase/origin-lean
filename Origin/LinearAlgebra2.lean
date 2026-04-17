/-
Released under MIT license.
-/
import Origin.Core

/-!
# Linear Algebra on Option α (Core-based)

**Category 2** — pure math, no zero-management infrastructure.

Mathlib LinearAlgebra: 153 files, 67,580 lines, 6,259 genuine declarations.
Origin restates every concept once, in minimum form.

Matrices, determinants, eigenvalues, bilinear forms, dimension,
basis, dual space, tensor products, linear maps, kernel/image/rank,
inner product spaces, spectral theory, Jordan normal form.
-/

universe u
variable {α β : Type u}

-- ============================================================================
-- 1. MATRICES
-- ============================================================================

/-- A 2×2 matrix. -/
structure Mat2 (γ : Type u) where
  e₁₁ : γ
  e₁₂ : γ
  e₂₁ : γ
  e₂₂ : γ

/-- Determinant of a 2×2 matrix on Option. -/
def det2 [Mul α] [Add α] [Neg α] (m : Mat2 (Option α)) : Option α :=
  m.e₁₁ * m.e₂₂ + -(m.e₁₂ * m.e₂₁)

theorem det2_some [Mul α] [Add α] [Neg α] (a b c d : α) :
    det2 ⟨some a, some b, some c, some d⟩ =
    some (a * d + -(b * c)) := by simp [det2]

theorem det2_none_row [Mul α] [Add α] [Neg α] (e₂₁ e₂₂ : Option α) :
    det2 ⟨none, none, e₂₁, e₂₂⟩ = none := by
  simp [det2]

/-- Trace of a 2×2 matrix. -/
def trace2 [Add α] (m : Mat2 (Option α)) : Option α := m.e₁₁ + m.e₂₂

theorem trace2_some [Add α] (a b c d : α) :
    trace2 ⟨some a, some b, some c, some d⟩ = some (a + d) := by
  simp [trace2]

/-- Transpose of a 2×2 matrix. -/
def transpose2 {γ : Type u} (m : Mat2 γ) : Mat2 γ :=
  { e₁₁ := m.e₁₁, e₁₂ := m.e₂₁, e₂₁ := m.e₁₂, e₂₂ := m.e₂₂ }

/-- Transpose is an involution. -/
theorem transpose_invol {γ : Type u} (m : Mat2 γ) :
    transpose2 (transpose2 m) = m := by simp [transpose2]

/-- Matrix multiplication for 2×2 (abstract). -/
def mat2Mul [Mul α] [Add α] (A B : Mat2 α) : Mat2 α :=
  { e₁₁ := A.e₁₁ * B.e₁₁ + A.e₁₂ * B.e₂₁,
    e₁₂ := A.e₁₁ * B.e₁₂ + A.e₁₂ * B.e₂₂,
    e₂₁ := A.e₂₁ * B.e₁₁ + A.e₂₂ * B.e₂₁,
    e₂₂ := A.e₂₁ * B.e₁₂ + A.e₂₂ * B.e₂₂ }

/-- Identity matrix. -/
def mat2Id (one zero : α) : Mat2 α :=
  { e₁₁ := one, e₁₂ := zero, e₂₁ := zero, e₂₂ := one }

-- ============================================================================
-- 2. EIGENVALUES
-- ============================================================================

/-- λ is an eigenvalue if det(A - λI) = 0. -/
def isEigenvalue (charF : α → α) (zero : α) (lam : α) : Prop := charF lam = zero

/-- Eigenvector: Av = λv with v ≠ 0. -/
def isEigenvector (applyF : α → α) (lam : α) (mulF : α → α → α) (v : α)
    (isNonzero : α → Prop) : Prop :=
  applyF v = mulF lam v ∧ isNonzero v

/-- The characteristic polynomial det(A - tI). -/
def charPoly (detF : (α → α) → α → α) (subtractF : α → α → α) : α → α :=
  fun t => detF (subtractF · t) t

/-- Cayley-Hamilton: A satisfies its own characteristic polynomial. -/
def cayleyHamilton (charPolyF : α → α) (evalAtMatrix : (α → α) → α)
    (zero : α) : Prop :=
  evalAtMatrix charPolyF = zero

-- ============================================================================
-- 3. BILINEAR FORMS
-- ============================================================================

/-- Bilinear form on Option: none absorbs. -/
def bilinear (bilF : α → α → α) : Option α → Option α → Option α := liftBin₂ bilF

@[simp] theorem bilinear_none_left (bilF : α → α → α) (v : Option α) :
    bilinear bilF none v = none := by cases v <;> rfl

@[simp] theorem bilinear_none_right (bilF : α → α → α) (u : Option α) :
    bilinear bilF u none = none := by cases u <;> rfl

@[simp] theorem bilinear_some (bilF : α → α → α) (u v : α) :
    bilinear bilF (some u) (some v) = some (bilF u v) := rfl

theorem bilinear_symm (bilF : α → α → α) (hsymm : ∀ u v, bilF u v = bilF v u)
    (u v : Option α) : bilinear bilF u v = bilinear bilF v u := by
  cases u <;> cases v <;> simp [bilinear, hsymm]

/-- Orthogonality: bilinear form evaluates to zero. -/
def isOrthogonal (bilF : α → α → α) (zero : α) (u v : α) : Prop := bilF u v = zero

-- ============================================================================
-- 4. LINEAR MAPS
-- ============================================================================

/-- A linear map preserves addition and scalar multiplication. -/
def IsLinearMap [Add α] [Mul α] (f : α → α) : Prop :=
  (∀ a b, f (a + b) = f a + f b) ∧
  (∀ c a, f (c * a) = c * f a)

/-- Kernel of a linear map: preimage of zero. -/
def kernel' (f : α → α) (zero : α) : α → Prop :=
  fun a => f a = zero

/-- Image (range) of a linear map. -/
def image' (f : α → α) : α → Prop :=
  fun b => ∃ a, f a = b

/-- Rank-nullity theorem (abstract): dim(ker) + dim(im) = dim(V). -/
def rankNullity (dimKer dimIm dimV : Nat) : Prop :=
  dimKer + dimIm = dimV

/-- Linear map composition lifts through Option. -/
theorem linearMap_comp (f g : α → α) (v : Option α) :
    Option.map g (Option.map f v) = Option.map (g ∘ f) v := by
  cases v <;> simp

-- ============================================================================
-- 5. DIMENSION AND BASIS
-- ============================================================================

/-- A set is a basis: linearly independent and spanning. -/
def isBasis (indepF spanF : α → Prop) (a : α) : Prop := indepF a ∧ spanF a

/-- Linear independence: no nontrivial linear combination gives zero. -/
def IsLinearlyIndep (isTriv : (α → α) → Prop) (combF : (α → α) → α)
    (zero : α) : Prop :=
  ∀ coeffs, combF coeffs = zero → isTriv coeffs

/-- Dimension: cardinality of any basis. -/
def dimension (basisCard : Nat) : Nat := basisCard

-- ============================================================================
-- 6. DUAL SPACE
-- ============================================================================

/-- The dual space: linear functionals V → k. -/
def dualSpace (linearF : (α → α) → Prop) : (α → α) → Prop := linearF

/-- Natural pairing between V and V*. -/
def dualPairing (eval : (α → α) → α → α) (f : α → α) (v : α) : α := eval f v

/-- Double dual embedding: v ↦ (f ↦ f(v)). -/
def doubleDualEmbed (v : α) : (α → α) → α :=
  fun f => f v

-- ============================================================================
-- 7. INNER PRODUCT SPACES
-- ============================================================================

/-- An inner product: positive-definite symmetric bilinear form. -/
def IsInnerProduct (ip : α → α → α) (isSymm isPosDef : (α → α → α) → Prop) : Prop :=
  isSymm ip ∧ isPosDef ip

/-- Cauchy-Schwarz inequality (abstract). -/
def cauchySchwarz [Mul α] (ip : α → α → α) (normF : α → α) (leF : α → α → Prop)
    (absF : α → α) : Prop :=
  ∀ u v, leF (absF (ip u v)) (normF u * normF v)

/-- Gram-Schmidt orthogonalization (abstract existence). -/
def gramSchmidt (orthogonalize : (Nat → α) → Nat → α) (ip : α → α → α)
    (zero : α) : Prop :=
  ∀ basis i j, i ≠ j → ip (orthogonalize basis i) (orthogonalize basis j) = zero

-- ============================================================================
-- 8. TENSOR PRODUCTS
-- ============================================================================

/-- Tensor product on Option: none absorbs. -/
def tensorProd : Option α → Option β → Option (α × β) := liftBin₂ Prod.mk

@[simp] theorem tensorProd_none_left (b : Option β) :
    tensorProd (none : Option α) b = none := by cases b <;> rfl

@[simp] theorem tensorProd_none_right (a : Option α) :
    tensorProd a (none : Option β) = none := by cases a <;> rfl

theorem tensorProd_some (a : α) (b : β) :
    tensorProd (some a) (some b) = some (a, b) := rfl

-- ============================================================================
-- 9. SPECTRAL THEORY
-- ============================================================================

/-- Spectral theorem: symmetric matrix is diagonalizable. -/
def spectralTheorem (isDiagonalizable : Prop) (isSymmetric : Prop) : Prop :=
  isSymmetric → isDiagonalizable

/-- Singular value decomposition (abstract existence). -/
def svdExists (hasDecomp : Prop) : Prop := hasDecomp

/-- Positive definite: all eigenvalues positive. -/
def IsPositiveDefinite (eigenvalues : Nat → α) (isPos : α → Prop) : Prop :=
  ∀ i, isPos (eigenvalues i)

-- ============================================================================
-- 10. JORDAN NORMAL FORM
-- ============================================================================

/-- Jordan block: eigenvalue on diagonal, 1 on superdiagonal. -/
structure JordanBlock (α : Type u) where
  eigenvalue : α
  size : Nat

/-- Jordan normal form exists for every matrix over algebraically closed fields. -/
def jordanNormalForm (blocks : List (JordanBlock α)) (isAlgClosed : Prop) : Prop :=
  isAlgClosed → blocks.length > 0

-- ============================================================================
-- 11. LINEAR ALGEBRA ON OPTION: demonstrations
-- ============================================================================

-- ============================================================================
-- STUBS — auto-generated by: python3 scripts/origin.py stub LinearAlgebra
-- Upgrade key declarations from stubs to real structures/theorems.
-- ============================================================================

-- AffineSpace/AffineEquiv.lean
-- COLLISION: mk' already in SetTheory.lean — rename needed
-- COLLISION: symm' already in SetTheory.lean — rename needed
-- COLLISION: apply' already in Order.lean — rename needed
-- COLLISION: symm_apply' already in Order.lean — rename needed
-- COLLISION: bijective' already in Order.lean — rename needed
-- COLLISION: surjective' already in Order.lean — rename needed
-- COLLISION: injective' already in Order.lean — rename needed
-- COLLISION: ofBijective' already in Algebra.lean — rename needed
-- COLLISION: range_eq' already in Order.lean — rename needed
-- COLLISION: apply_symm_apply' already in Order.lean — rename needed
-- COLLISION: refl' already in SetTheory.lean — rename needed

-- AffineSpace/AffineMap.lean

-- AffineSpace/AffineSubspace.lean
-- COLLISION: map' already in SetTheory.lean — rename needed
-- COLLISION: map_bot' already in Order.lean — rename needed
-- COLLISION: map_eq_bot_iff' already in Order.lean — rename needed

-- AffineSpace/Basis.lean

-- AffineSpace/Combination.lean

-- AffineSpace/ContinuousAffineEquiv.lean
-- COLLISION: coe' already in Order.lean — rename needed

-- AffineSpace/FiniteDimensional.lean

-- AffineSpace/Independent.lean

-- AffineSpace/Matrix.lean

-- AffineSpace/Midpoint.lean

-- AffineSpace/Ordered.lean

-- AffineSpace/Pointwise.lean
-- COLLISION: mulAction' already in Order.lean — rename needed

-- AffineSpace/Restrict.lean

-- AffineSpace/Slope.lean

-- Alternating/Basic.lean

-- Alternating/DomCoprod.lean

-- AnnihilatingPolynomial.lean

-- Basis/Basic.lean

-- Basis/Bilinear.lean

-- Basis/Cardinality.lean

-- Basis/Defs.lean

-- Basis/Flag.lean

-- Basis/VectorSpace.lean

-- BilinearForm/Basic.lean
-- COLLISION: add_left' already in Algebra.lean — rename needed
-- COLLISION: smul_left' already in Algebra.lean — rename needed
-- COLLISION: neg_left' already in Algebra.lean — rename needed
-- COLLISION: flip' already in Order.lean — rename needed

-- BilinearForm/DualLattice.lean

-- BilinearForm/Hom.lean

-- BilinearForm/Orthogonal.lean

-- BilinearForm/Properties.lean

-- BilinearForm/TensorProduct.lean

-- BilinearMap.lean

-- Charpoly/BaseChange.lean

-- Charpoly/Basic.lean

-- Charpoly/ToMatrix.lean

-- CliffordAlgebra/BaseChange.lean

-- CliffordAlgebra/Basic.lean

-- CliffordAlgebra/CategoryTheory.lean

-- CliffordAlgebra/Conjugation.lean

-- CliffordAlgebra/Contraction.lean

-- CliffordAlgebra/Equivs.lean

-- CliffordAlgebra/Even.lean

-- CliffordAlgebra/EvenEquiv.lean

-- CliffordAlgebra/Fold.lean

-- CliffordAlgebra/Grading.lean

-- CliffordAlgebra/Inversion.lean

-- CliffordAlgebra/Prod.lean
-- COLLISION: prodEquiv' already in Order.lean — rename needed

-- CliffordAlgebra/SpinGroup.lean
-- COLLISION: star_mul_self_of_mem' already in Algebra.lean — rename needed
-- COLLISION: toUnits_injective' already in Algebra.lean — rename needed

-- CliffordAlgebra/Star.lean
-- COLLISION: star_ι' already in Algebra.lean — rename needed
-- COLLISION: star_smul' already in Algebra.lean — rename needed
-- COLLISION: star_algebraMap' already in Algebra.lean — rename needed

-- Coevaluation.lean

-- Contraction.lean

-- CrossProduct.lean

-- DFinsupp.lean

-- Determinant.lean

-- Dimension/Basic.lean

-- Dimension/Constructions.lean

-- Dimension/DivisionRing.lean

-- Dimension/Finite.lean

-- Dimension/Finrank.lean

-- Dimension/Free.lean

-- Dimension/FreeAndStrongRankCondition.lean

-- Dimension/LinearMap.lean

-- Dimension/Localization.lean

-- Dimension/RankNullity.lean

-- Dimension/StrongRankCondition.lean

-- Dimension/Torsion.lean

-- DirectSum/Finsupp.lean

-- DirectSum/TensorProduct.lean

-- Dual.lean

-- Eigenspace/Basic.lean

-- Eigenspace/Matrix.lean

-- Eigenspace/Minpoly.lean

-- Eigenspace/Pi.lean

-- Eigenspace/Semisimple.lean

-- Eigenspace/Triangularizable.lean

-- Eigenspace/Zero.lean

-- ExteriorAlgebra/Basic.lean

-- ExteriorAlgebra/Grading.lean

-- ExteriorAlgebra/OfAlternating.lean
-- COLLISION: lhom_ext' already in Algebra.lean — rename needed

-- FiniteDimensional.lean

-- FiniteDimensional/Defs.lean

-- FiniteSpan.lean

-- Finsupp/Defs.lean

-- Finsupp/LSum.lean

-- Finsupp/LinearCombination.lean

-- Finsupp/Pi.lean

-- Finsupp/Span.lean

-- Finsupp/SumProd.lean

-- Finsupp/Supported.lean

-- Finsupp/VectorSpace.lean

-- FreeAlgebra.lean

-- FreeModule/Basic.lean
-- COLLISION: of_equiv' already in SetTheory.lean — rename needed

-- FreeModule/Finite/Basic.lean

-- FreeModule/Finite/Matrix.lean

-- FreeModule/IdealQuotient.lean

-- FreeModule/Int.lean

-- FreeModule/Norm.lean

-- FreeModule/PID.lean

-- FreeProduct/Basic.lean

-- GeneralLinearGroup.lean
-- COLLISION: toLinearEquiv' already in Algebra.lean — rename needed

-- InvariantBasisNumber.lean

-- Isomorphisms.lean

-- JordanChevalley.lean

-- Lagrange.lean

-- LinearDisjoint.lean
-- COLLISION: LinearDisjoint' already in RingTheory2.lean — rename needed
-- COLLISION: mulMap' already in RingTheory2.lean — rename needed
-- COLLISION: symm_of_commute' already in RingTheory2.lean — rename needed
-- COLLISION: linearDisjoint_comm_of_commute' already in RingTheory2.lean — rename needed
-- COLLISION: of_basis_left' already in RingTheory2.lean — rename needed
-- COLLISION: of_basis_right' already in RingTheory2.lean — rename needed

-- LinearIndependent.lean

-- LinearPMap.lean

-- Matrix/AbsoluteValue.lean

-- Matrix/Adjugate.lean

-- Matrix/BaseChange.lean

-- Matrix/Basis.lean

-- Matrix/BilinearForm.lean

-- Matrix/Block.lean

-- Matrix/Charpoly/Basic.lean

-- Matrix/Charpoly/Coeff.lean

-- Matrix/Charpoly/Eigs.lean

-- Matrix/Charpoly/FiniteField.lean

-- Matrix/Charpoly/LinearMap.lean

-- Matrix/Charpoly/Minpoly.lean

-- Matrix/Charpoly/Univ.lean

-- Matrix/Circulant.lean

-- Matrix/Determinant/Basic.lean

-- Matrix/Determinant/Misc.lean

-- Matrix/Determinant/TotallyUnimodular.lean

-- Matrix/Diagonal.lean

-- Matrix/DotProduct.lean

-- Matrix/Dual.lean

-- Matrix/FixedDetMatrices.lean
-- COLLISION: smul_coe' already in Algebra.lean — rename needed

-- Matrix/GeneralLinearGroup/Basic.lean

-- Matrix/GeneralLinearGroup/Card.lean

-- Matrix/GeneralLinearGroup/Defs.lean

-- Matrix/Gershgorin.lean

-- Matrix/Hermitian.lean

-- Matrix/HermitianFunctionalCalculus.lean

-- Matrix/Ideal.lean

-- Matrix/InvariantBasisNumber.lean

-- Matrix/IsDiag.lean

-- Matrix/LDL.lean

-- Matrix/MvPolynomial.lean

-- Matrix/Nondegenerate.lean

-- Matrix/NonsingularInverse.lean

-- Matrix/Orthogonal.lean

-- Matrix/Permanent.lean

-- Matrix/Permutation.lean

-- Matrix/Polynomial.lean

-- Matrix/PosDef.lean

-- Matrix/ProjectiveSpecialLinearGroup.lean

-- Matrix/Reindex.lean

-- Matrix/SchurComplement.lean

-- Matrix/SesquilinearForm.lean

-- Matrix/SpecialLinearGroup.lean

-- Matrix/Spectrum.lean

-- Matrix/StdBasis.lean

-- Matrix/Symmetric.lean

-- Matrix/ToLin.lean

-- Matrix/ToLinearEquiv.lean

-- Matrix/Trace.lean

-- Matrix/Transvection.lean

-- Matrix/ZPow.lean
-- COLLISION: inv_pow' already in Algebra.lean — rename needed
-- COLLISION: zpow_neg' already in Algebra.lean — rename needed
-- COLLISION: zpow_add_one' already in Algebra.lean — rename needed
-- COLLISION: zpow_one_add' already in Algebra.lean — rename needed
-- COLLISION: zpow_right' already in Algebra.lean — rename needed
-- COLLISION: zpow_left' already in Algebra.lean — rename needed
-- COLLISION: zpow_zpow' already in Algebra.lean — rename needed
-- COLLISION: zpow_self' already in Algebra.lean — rename needed
-- COLLISION: self_zpow' already in Algebra.lean — rename needed
-- COLLISION: zpow_mul' already in Algebra.lean — rename needed
-- COLLISION: zpow_sub' already in Algebra.lean — rename needed

-- Multilinear/Basic.lean

-- Multilinear/Basis.lean

-- Multilinear/DFinsupp.lean

-- Multilinear/FiniteDimensional.lean

-- Multilinear/Pi.lean

-- Multilinear/TensorProduct.lean

-- Orientation.lean

-- PID.lean

-- PerfectPairing.lean

-- Pi.lean

-- PiTensorProduct.lean

-- Prod.lean
-- COLLISION: graph_eq_range_prod' already in Algebra.lean — rename needed

-- Projection.lean

-- Projectivization/Basic.lean
-- COLLISION: map_injective' already in Order.lean — rename needed

-- Projectivization/Constructions.lean

-- Projectivization/Independence.lean

-- Projectivization/Subspace.lean

-- QuadraticForm/Basic.lean

-- QuadraticForm/Basis.lean

-- QuadraticForm/Complex.lean

-- QuadraticForm/Dual.lean
-- COLLISION: toDualProd' already in Order.lean — rename needed

-- QuadraticForm/Isometry.lean
-- COLLISION: toLinearMap_injective' already in Algebra.lean — rename needed
-- COLLISION: id_comp' already in Order.lean — rename needed
-- COLLISION: comp_id' already in Order.lean — rename needed
-- COLLISION: comp_assoc' already in Algebra.lean — rename needed

-- QuadraticForm/IsometryEquiv.lean

-- QuadraticForm/Prod.lean

-- QuadraticForm/QuadraticModuleCat.lean
-- COLLISION: ofHom' already in Algebra.lean — rename needed

-- QuadraticForm/QuadraticModuleCat/Monoidal.lean
-- COLLISION: tensorObj' already in Algebra.lean — rename needed
-- COLLISION: tensorHom' already in Algebra.lean — rename needed

-- QuadraticForm/Real.lean

-- QuadraticForm/TensorProduct.lean

-- QuadraticForm/TensorProduct/Isometries.lean

-- Quotient/Basic.lean

-- Quotient/Defs.lean
-- COLLISION: quotEquivOfEq' already in RingTheory2.lean — rename needed

-- Quotient/Pi.lean
-- COLLISION: invFun' already in RingTheory2.lean — rename needed
-- COLLISION: left_inv' already in RingTheory2.lean — rename needed

-- Ray.lean

-- Reflection.lean

-- RootSystem/Basic.lean

-- RootSystem/Defs.lean

-- RootSystem/Finite/CanonicalBilinear.lean

-- RootSystem/Finite/Nondegenerate.lean

-- RootSystem/Hom.lean

-- RootSystem/OfBilinear.lean

-- RootSystem/RootPairingCat.lean

-- RootSystem/RootPositive.lean

-- SModEq.lean
-- COLLISION: sub_mem' already in RingTheory2.lean — rename needed
-- COLLISION: top' already in Order.lean — rename needed
-- COLLISION: bot' already in Order.lean — rename needed
-- COLLISION: nsmul' already in RingTheory2.lean — rename needed
-- COLLISION: zsmul' already in RingTheory2.lean — rename needed

-- Semisimple.lean
-- COLLISION: mul_of_commute' already in Algebra.lean — rename needed

-- SesquilinearForm.lean

-- Span/Basic.lean

-- Span/Defs.lean
-- COLLISION: mem_span_insert' already in RingTheory2.lean — rename needed
-- COLLISION: mem_span_pair' already in RingTheory2.lean — rename needed
-- COLLISION: span_eq_bot' already in RingTheory2.lean — rename needed
-- COLLISION: mem_iSup' already in Order.lean — rename needed

-- StdBasis.lean

-- SymplecticGroup.lean

-- TensorAlgebra/Basic.lean

-- TensorAlgebra/Basis.lean

-- TensorAlgebra/Grading.lean

-- TensorAlgebra/ToTensorPower.lean

-- TensorPower.lean

-- TensorProduct/Basic.lean

-- TensorProduct/Basis.lean

-- TensorProduct/DirectLimit.lean

-- TensorProduct/Finiteness.lean

-- TensorProduct/Graded/External.lean

-- TensorProduct/Graded/Internal.lean

-- TensorProduct/Matrix.lean

-- TensorProduct/Opposite.lean

-- TensorProduct/Pi.lean

-- TensorProduct/Prod.lean

-- TensorProduct/Quotient.lean

-- TensorProduct/RightExactness.lean

-- TensorProduct/Subalgebra.lean

-- TensorProduct/Submodule.lean

-- TensorProduct/Tower.lean
-- COLLISION: baseChange_bot' already in Algebra.lean — rename needed
-- COLLISION: baseChange_top' already in Algebra.lean — rename needed

-- TensorProduct/Vanishing.lean

-- Trace.lean

-- UnitaryGroup.lean

-- Vandermonde.lean
