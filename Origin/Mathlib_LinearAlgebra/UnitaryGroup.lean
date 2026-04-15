/-
Extracted from LinearAlgebra/UnitaryGroup.lean
Genuine: 9 of 11 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# The Unitary Group

This file defines elements of the unitary group `Matrix.unitaryGroup n α`, where `α` is a
`StarRing`. This consists of all `n` by `n` matrices with entries in `α` such that the
star-transpose is its inverse. In addition, we define the group structure on
`Matrix.unitaryGroup n α`, and the embedding into the general linear group
`LinearMap.GeneralLinearGroup α (n → α)`.

We also define the orthogonal group `Matrix.orthogonalGroup n R`, where `R` is a `CommRing`.

## Main Definitions

* `Matrix.unitaryGroup` is the submonoid of matrices where the star-transpose is the inverse; the
  group structure (under multiplication) is inherited from a more general `unitary` construction.
* `Matrix.UnitaryGroup.embeddingGL` is the embedding `Matrix.unitaryGroup n α → GLₙ(α)`, where
  `GLₙ(α)` is `LinearMap.GeneralLinearGroup α (n → α)`.
* `Matrix.orthogonalGroup` is the submonoid of matrices where the transpose is the inverse.

## References

* https://en.wikipedia.org/wiki/Unitary_group

## Tags

matrix group, group, unitary group, orthogonal group

-/

universe u v

namespace Matrix

open LinearMap Matrix

variable (n : Type u) [DecidableEq n] [Fintype n]

variable (α : Type v) [CommRing α] [StarRing α]

abbrev unitaryGroup : Submonoid (Matrix n n α) :=
  unitary (Matrix n n α)

example : Group (unitaryGroup n α) := inferInstance

example : StarMul (unitaryGroup n α) := inferInstance

end

variable {n : Type u} [DecidableEq n] [Fintype n]

variable {α : Type v} [CommRing α] [StarRing α] {A : Matrix n n α}

theorem mem_unitaryGroup_iff : A ∈ Matrix.unitaryGroup n α ↔ A * star A = 1 := by
  refine ⟨And.right, fun hA => ⟨?_, hA⟩⟩
  simpa only [mul_eq_one_comm] using hA

theorem mem_unitaryGroup_iff' : A ∈ Matrix.unitaryGroup n α ↔ star A * A = 1 := by
  refine ⟨And.left, fun hA => ⟨hA, ?_⟩⟩
  rwa [mul_eq_one_comm] at hA

theorem det_of_mem_unitary {A : Matrix n n α} (hA : A ∈ Matrix.unitaryGroup n α) :
    A.det ∈ unitary α := by
  constructor
  · simpa [star, det_transpose] using congr_arg det hA.1
  · simpa [star, det_transpose] using congr_arg det hA.2

open scoped Kronecker in

theorem kronecker_mem_unitary {R m : Type*} [Semiring R] [StarRing R] [Fintype m]
    [DecidableEq m] {U₁ : Matrix n n R} {U₂ : Matrix m m R}
    (hU₁ : U₁ ∈ unitary (Matrix n n R)) (hU₂ : U₂ ∈ unitary (Matrix m m R)) :
    U₁ ⊗ₖ U₂ ∈ unitary (Matrix (n × m) (n × m) R) := by
  simp_rw [Unitary.mem_iff, star_eq_conjTranspose, conjTranspose_kronecker']
  constructor <;> ext <;> simp only [mul_apply, submatrix_apply, kroneckerMap_apply, Prod.fst_swap,
    conjTranspose_apply, ← star_apply, Prod.snd_swap, ← mul_assoc]
  · simp_rw [mul_assoc _ (star U₁ _ _), ← Finset.univ_product_univ, Finset.sum_product]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, ← Finset.mul_sum, ← Matrix.mul_apply, hU₁.1, Matrix.one_apply,
      mul_boole, ite_mul, zero_mul, Finset.sum_ite_irrel, ← Matrix.mul_apply, hU₂.1,
      Matrix.one_apply, Finset.sum_const_zero, ← ite_and, Prod.eq_iff_fst_eq_snd_eq]
  · simp_rw [mul_assoc _ _ (star U₂ _ _), ← Finset.univ_product_univ, Finset.sum_product,
      ← Finset.sum_mul, ← Finset.mul_sum, ← Matrix.mul_apply, hU₂.2, Matrix.one_apply, mul_boole,
      ite_mul, zero_mul, Finset.sum_ite_irrel, ← Matrix.mul_apply, hU₁.2, Matrix.one_apply,
      Finset.sum_const_zero, ← ite_and, and_comm, Prod.eq_iff_fst_eq_snd_eq]

section TensorProduct

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
  [StarRing A] [StarRing B] [StarRing R] [StarModule R A] [StarModule R B]

open scoped TensorProduct Kronecker

theorem _root_.Unitary.tmul_mem {U : A} {V : B} (hU : U ∈ unitary A) (hV : V ∈ unitary B) :
    U ⊗ₜ[R] V ∈ unitary (A ⊗[R] B) := by
  simp [Unitary.mem_iff, hU, hV, Algebra.TensorProduct.one_def]

theorem kroneckerTMul_mem_unitary {m : Type*} [Fintype m] [DecidableEq m] {U : Matrix m m A}
    {V : Matrix n n B} (hU : U ∈ unitary (Matrix m m A)) (hV : V ∈ unitary (Matrix n n B)) :
    U ⊗ₖₜ[R] V ∈ unitary (Matrix (m × n) (m × n) (A ⊗[R] B)) := by
  simp_rw [Unitary.mem_iff, star_eq_conjTranspose] at hU hV ⊢
  simp [conjTranspose_kroneckerTMul, ← mul_kroneckerTMul_mul, hU, hV]

end TensorProduct

namespace UnitaryGroup

-- INSTANCE (free from Core): coeMatrix

-- INSTANCE (free from Core): coeFun

def toLin' (A : unitaryGroup n α) :=
  Matrix.toLin' A.1

theorem ext_iff (A B : unitaryGroup n α) : A = B ↔ ∀ i j, A i j = B i j :=
  Subtype.ext_iff.trans ⟨fun h i j => congr_fun (congr_fun h i) j, Matrix.ext⟩
