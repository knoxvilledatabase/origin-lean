/-
Extracted from LinearAlgebra/TensorProduct/Basis.lean
Genuine: 23 of 23 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
# Bases and dimensionality of tensor products of modules

These can not go into `LinearAlgebra.TensorProduct` since they depend on
`LinearAlgebra.FinsuppVectorSpace` which in turn imports `LinearAlgebra.TensorProduct`.
-/

noncomputable section

open Set LinearMap Submodule

open scoped TensorProduct

section CommSemiring

variable {R : Type*} {S : Type*} {M : Type*} {N : Type*} {ι : Type*} {κ : Type*}
  [CommSemiring R] [Semiring S] [Algebra R S] [AddCommMonoid M] [Module R M] [Module S M]
  [IsScalarTower R S M] [AddCommMonoid N] [Module R N]

def Basis.tensorProduct (b : Basis ι S M) (c : Basis κ R N) :
    Basis (ι × κ) S (M ⊗[R] N) :=
  Finsupp.basisSingleOne.map
    ((TensorProduct.AlgebraTensorModule.congr b.repr c.repr).trans <|
        (finsuppTensorFinsupp R S _ _ _ _).trans <|
          Finsupp.lcongr (Equiv.refl _) (TensorProduct.AlgebraTensorModule.rid R S S)).symm

@[simp]
theorem Basis.tensorProduct_apply (b : Basis ι S M) (c : Basis κ R N) (i : ι) (j : κ) :
    Basis.tensorProduct b c (i, j) = b i ⊗ₜ c j := by
  simp [Basis.tensorProduct]

theorem Basis.tensorProduct_apply' (b : Basis ι S M) (c : Basis κ R N) (i : ι × κ) :
    Basis.tensorProduct b c i = b i.1 ⊗ₜ c i.2 := by
  simp [Basis.tensorProduct]

@[simp]
theorem Basis.tensorProduct_repr_tmul_apply (b : Basis ι S M) (c : Basis κ R N) (m : M) (n : N)
    (i : ι) (j : κ) :
    (Basis.tensorProduct b c).repr (m ⊗ₜ n) (i, j) = c.repr n j • b.repr m i := by
  simp [Basis.tensorProduct, mul_comm]

variable (S : Type*) [Semiring S] [Algebra R S]

noncomputable

def Basis.baseChange (b : Basis ι R M) : Basis ι S (S ⊗[R] M) :=
  ((Basis.singleton Unit S).tensorProduct b).reindex (Equiv.punitProd ι)

@[simp]
lemma Basis.baseChange_repr_tmul (b : Basis ι R M) (x y i) :
    (b.baseChange S).repr (x ⊗ₜ y) i = b.repr y i • x := by
  simp [Basis.baseChange, Basis.tensorProduct]

@[simp]
lemma Basis.baseChange_apply (b : Basis ι R M) (i) :
    b.baseChange S i = 1 ⊗ₜ b i := by
  simp [Basis.baseChange, Basis.tensorProduct]

section

variable [DecidableEq ι] [DecidableEq κ]

variable (ℬ : Basis ι R M) (𝒞 : Basis κ R N) (x : M ⊗[R] N)

def TensorProduct.equivFinsuppOfBasisRight : M ⊗[R] N ≃ₗ[R] κ →₀ M :=
  LinearEquiv.lTensor M 𝒞.repr ≪≫ₗ TensorProduct.finsuppScalarRight R M κ

@[simp]
lemma TensorProduct.equivFinsuppOfBasisRight_apply_tmul (m : M) (n : N) :
    (TensorProduct.equivFinsuppOfBasisRight 𝒞) (m ⊗ₜ n) =
    (𝒞.repr n).mapRange (· • m) (zero_smul _ _) := by
  ext; simp [equivFinsuppOfBasisRight]

lemma TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply
    (m : M) (n : N) (i : κ) :
    (TensorProduct.equivFinsuppOfBasisRight 𝒞) (m ⊗ₜ n) i =
    𝒞.repr n i • m := by
  simp only [equivFinsuppOfBasisRight_apply_tmul, Finsupp.mapRange_apply]

lemma TensorProduct.equivFinsuppOfBasisRight_symm :
    (TensorProduct.equivFinsuppOfBasisRight 𝒞).symm.toLinearMap =
    Finsupp.lsum R fun i ↦ (TensorProduct.mk R M N).flip (𝒞 i) := by
  ext; simp [equivFinsuppOfBasisRight]

@[simp]
lemma TensorProduct.equivFinsuppOfBasisRight_symm_apply (b : κ →₀ M) :
    (TensorProduct.equivFinsuppOfBasisRight 𝒞).symm b = b.sum fun i m ↦ m ⊗ₜ 𝒞 i :=
  congr($(TensorProduct.equivFinsuppOfBasisRight_symm 𝒞) b)

lemma TensorProduct.sum_tmul_basis_right_injective :
    Function.Injective (Finsupp.lsum R fun i ↦ (TensorProduct.mk R M N).flip (𝒞 i)) :=
  (equivFinsuppOfBasisRight_symm (M := M) 𝒞).symm ▸
    (TensorProduct.equivFinsuppOfBasisRight 𝒞).symm.injective

lemma TensorProduct.sum_tmul_basis_right_eq_zero
    (b : κ →₀ M) (h : (b.sum fun i m ↦ m ⊗ₜ[R] 𝒞 i) = 0) : b = 0 :=
  (TensorProduct.equivFinsuppOfBasisRight 𝒞).symm.injective (a₂ := 0) <| by simpa

def TensorProduct.equivFinsuppOfBasisLeft : M ⊗[R] N ≃ₗ[R] ι →₀ N :=
  TensorProduct.comm R M N ≪≫ₗ TensorProduct.equivFinsuppOfBasisRight ℬ

@[simp]
lemma TensorProduct.equivFinsuppOfBasisLeft_apply_tmul (m : M) (n : N) :
    (TensorProduct.equivFinsuppOfBasisLeft ℬ) (m ⊗ₜ n) =
    (ℬ.repr m).mapRange (· • n) (zero_smul _ _) := by
  ext; simp [equivFinsuppOfBasisLeft]

lemma TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply
    (m : M) (n : N) (i : ι) :
    (TensorProduct.equivFinsuppOfBasisLeft ℬ) (m ⊗ₜ n) i =
    ℬ.repr m i • n := by
  simp only [equivFinsuppOfBasisLeft_apply_tmul, Finsupp.mapRange_apply]

lemma TensorProduct.equivFinsuppOfBasisLeft_symm :
    (TensorProduct.equivFinsuppOfBasisLeft ℬ).symm.toLinearMap =
    Finsupp.lsum R fun i ↦ (TensorProduct.mk R M N) (ℬ i) := by
  ext; simp [equivFinsuppOfBasisLeft]

@[simp]
lemma TensorProduct.equivFinsuppOfBasisLeft_symm_apply (b : ι →₀ N) :
    (TensorProduct.equivFinsuppOfBasisLeft ℬ).symm b = b.sum fun i n ↦ ℬ i ⊗ₜ n :=
  congr($(TensorProduct.equivFinsuppOfBasisLeft_symm ℬ) b)

lemma TensorProduct.eq_repr_basis_right :
    ∃ b : κ →₀ M, b.sum (fun i m ↦ m ⊗ₜ 𝒞 i) = x := by
  simpa using (TensorProduct.equivFinsuppOfBasisRight 𝒞).symm.surjective x

lemma TensorProduct.eq_repr_basis_left :
    ∃ (c : ι →₀ N), (c.sum fun i n ↦ ℬ i ⊗ₜ n) = x := by
  obtain ⟨c, rfl⟩ := (TensorProduct.equivFinsuppOfBasisLeft ℬ).symm.surjective x
  exact ⟨c, (TensorProduct.comm R M N).injective <| by simp [Finsupp.sum]⟩

lemma TensorProduct.sum_tmul_basis_left_injective :
    Function.Injective (Finsupp.lsum R fun i ↦ (TensorProduct.mk R M N) (ℬ i)) :=
  (equivFinsuppOfBasisLeft_symm (N := N) ℬ).symm ▸
    (TensorProduct.equivFinsuppOfBasisLeft ℬ).symm.injective

lemma TensorProduct.sum_tmul_basis_left_eq_zero
    (b : ι →₀ N) (h : (b.sum fun i n ↦ ℬ i ⊗ₜ[R] n) = 0) : b = 0 :=
  (TensorProduct.equivFinsuppOfBasisLeft ℬ).symm.injective (a₂ := 0) <| by simpa

end

end CommSemiring

end
