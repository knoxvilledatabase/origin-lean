/-
Extracted from LinearAlgebra/CliffordAlgebra/Prod.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Clifford algebras of a direct sum of two vector spaces

We show that the Clifford algebra of a direct sum is the graded tensor product of the Clifford
algebras, as `CliffordAlgebra.equivProd`.

## Main definitions:

* `CliffordAlgebra.equivProd : CliffordAlgebra (Q₁.prod Q₂) ≃ₐ[R] (evenOdd Q₁ ᵍ⊗[R] evenOdd Q₂)`

## TODO

Introduce morphisms and equivalences of graded algebras, and upgrade `CliffordAlgebra.equivProd`
to a graded algebra equivalence.

-/

suppress_compilation

variable {R M₁ M₂ N : Type*}

variable [CommRing R] [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup N]

variable [Module R M₁] [Module R M₂] [Module R N]

variable (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) (Qₙ : QuadraticForm R N)

open scoped TensorProduct

namespace CliffordAlgebra

section map_mul_map

variable {Q₁ Q₂ Qₙ}

variable (f₁ : Q₁ →qᵢ Qₙ) (f₂ : Q₂ →qᵢ Qₙ) (hf : ∀ x y, Qₙ.IsOrtho (f₁ x) (f₂ y))

variable (m₁ : CliffordAlgebra Q₁) (m₂ : CliffordAlgebra Q₂)

include hf

nonrec theorem map_mul_map_of_isOrtho_of_mem_evenOdd
    {i₁ i₂ : ZMod 2} (hm₁ : m₁ ∈ evenOdd Q₁ i₁) (hm₂ : m₂ ∈ evenOdd Q₂ i₂) :
    map f₁ m₁ * map f₂ m₂ = (-1 : ℤˣ) ^ (i₂ * i₁) • (map f₂ m₂ * map f₁ m₁) := by
  -- for each variable, induct on powers of `ι`, then on the exponent of each power
  induction hm₁ using Submodule.iSup_induction' with
  | zero => rw [map_zero, zero_mul, mul_zero, smul_zero]
  | add _ _ _ _ ihx ihy => rw [map_add, add_mul, mul_add, ihx, ihy, smul_add]
  | mem i₁' m₁' hm₁ =>
    obtain ⟨i₁n, rfl⟩ := i₁'
    dsimp only at *
    induction hm₁ using Submodule.pow_induction_on_left' with
    | algebraMap =>
      rw [AlgHom.commutes, Nat.cast_zero, mul_zero, uzpow_zero, one_smul, Algebra.commutes]
    | add _ _ _ _ _ ihx ihy =>
      rw [map_add, add_mul, mul_add, ihx, ihy, smul_add]
    | mem_mul m₁ hm₁ i x₁ _hx₁ ih₁ =>
      obtain ⟨v₁, rfl⟩ := hm₁
      -- This is the first interesting goal.
      rw [map_mul, mul_assoc, ih₁, mul_smul_comm, map_apply_ι, Nat.cast_succ, mul_add_one,
        uzpow_add, mul_smul, ← mul_assoc, ← mul_assoc, ← smul_mul_assoc ((-1) ^ i₂)]
      clear ih₁
      congr 2
      induction hm₂ using Submodule.iSup_induction' with
      | zero => rw [map_zero, zero_mul, mul_zero, smul_zero]
      | add _ _ _ _ ihx ihy => rw [map_add, add_mul, mul_add, ihx, ihy, smul_add]
      | mem i₂' m₂' hm₂ =>
        clear m₂
        obtain ⟨i₂n, rfl⟩ := i₂'
        dsimp only at *
        induction hm₂ using Submodule.pow_induction_on_left' with
        | algebraMap =>
          rw [AlgHom.commutes, Nat.cast_zero, uzpow_zero, one_smul, Algebra.commutes]
        | add _ _ _ _ _ ihx ihy =>
          rw [map_add, add_mul, mul_add, ihx, ihy, smul_add]
        | mem_mul m₂ hm₂ i x₂ _hx₂ ih₂ =>
          obtain ⟨v₂, rfl⟩ := hm₂
          -- This is the second interesting goal.
          rw [map_mul, map_apply_ι, Nat.cast_succ, ← mul_assoc,
            ι_mul_ι_comm_of_isOrtho (hf _ _), neg_mul, mul_assoc, ih₂, mul_smul_comm,
            ← mul_assoc, ← Units.neg_smul, uzpow_add, uzpow_one, mul_neg_one]

theorem commute_map_mul_map_of_isOrtho_of_mem_evenOdd_zero_left
    {i₂ : ZMod 2} (hm₁ : m₁ ∈ evenOdd Q₁ 0) (hm₂ : m₂ ∈ evenOdd Q₂ i₂) :
    Commute (map f₁ m₁) (map f₂ m₂) :=
  (map_mul_map_of_isOrtho_of_mem_evenOdd _ _ hf _ _ hm₁ hm₂).trans <| by simp

theorem commute_map_mul_map_of_isOrtho_of_mem_evenOdd_zero_right
    {i₁ : ZMod 2} (hm₁ : m₁ ∈ evenOdd Q₁ i₁) (hm₂ : m₂ ∈ evenOdd Q₂ 0) :
    Commute (map f₁ m₁) (map f₂ m₂) :=
  (map_mul_map_of_isOrtho_of_mem_evenOdd _ _ hf _ _ hm₁ hm₂).trans <| by simp

theorem map_mul_map_eq_neg_of_isOrtho_of_mem_evenOdd_one
    (hm₁ : m₁ ∈ evenOdd Q₁ 1) (hm₂ : m₂ ∈ evenOdd Q₂ 1) :
    map f₁ m₁ * map f₂ m₂ = -map f₂ m₂ * map f₁ m₁ := by
  simp [map_mul_map_of_isOrtho_of_mem_evenOdd _ _ hf _ _ hm₁ hm₂]

end map_mul_map

def ofProd : CliffordAlgebra (Q₁.prod Q₂) →ₐ[R] (evenOdd Q₁ ᵍ⊗[R] evenOdd Q₂) :=
  lift _ ⟨
    LinearMap.coprod
      ((GradedTensorProduct.includeLeft (evenOdd Q₁) (evenOdd Q₂)).toLinearMap
          ∘ₗ (evenOdd Q₁ 1).subtype ∘ₗ (ι Q₁).codRestrict _ (ι_mem_evenOdd_one Q₁))
      ((GradedTensorProduct.includeRight (evenOdd Q₁) (evenOdd Q₂)).toLinearMap
          ∘ₗ (evenOdd Q₂ 1).subtype ∘ₗ (ι Q₂).codRestrict _ (ι_mem_evenOdd_one Q₂)),
    fun m => by
      simp_rw [LinearMap.coprod_apply, LinearMap.coe_comp, Function.comp_apply,
        AlgHom.toLinearMap_apply, QuadraticMap.prod_apply, Submodule.coe_subtype,
        GradedTensorProduct.includeLeft_apply, GradedTensorProduct.includeRight_apply, map_add,
        add_mul, mul_add, GradedTensorProduct.algebraMap_def,
        GradedTensorProduct.tmul_one_mul_one_tmul, GradedTensorProduct.tmul_one_mul_coe_tmul,
        GradedTensorProduct.tmul_coe_mul_one_tmul, GradedTensorProduct.tmul_coe_mul_coe_tmul,
        LinearMap.codRestrict_apply, one_mul, uzpow_one, Units.neg_smul, one_smul, ι_sq_scalar,
        mul_one, ← GradedTensorProduct.algebraMap_def, ← GradedTensorProduct.algebraMap_def']
      abel⟩
