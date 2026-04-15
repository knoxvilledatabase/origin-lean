/-
Extracted from LinearAlgebra/Matrix/SesquilinearForm.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Sesquilinear form

This file defines the conversion between sesquilinear maps and matrices.

## Main definitions

* `Matrix.toLinearMap₂` given a basis define a bilinear map
* `Matrix.toLinearMap₂'` define the bilinear map on `n → R`
* `LinearMap.toMatrix₂`: calculate the matrix coefficients of a bilinear map
* `LinearMap.toMatrix₂'`: calculate the matrix coefficients of a bilinear map on `n → R`

## TODO

At the moment this is quite a literal port from `Matrix.BilinearForm`. Everything should be
generalized to fully semi-bilinear forms.

## Tags

Sesquilinear form, Sesquilinear map, matrix, basis

-/

open Finset LinearMap Matrix Module

open scoped RightActions

variable {R R₁ S₁ R₂ S₂ M₁ M₂ M₁' M₂' N₂ n m n' m' ι : Type*}

section AuxToLinearMap

variable [Semiring R₁] [Semiring S₁] [Semiring R₂] [Semiring S₂] [AddCommMonoid N₂]
  [Module S₁ N₂] [Module S₂ N₂] [SMulCommClass S₂ S₁ N₂]

variable [Fintype n] [Fintype m]

variable (σ₁ : R₁ →+* S₁) (σ₂ : R₂ →+* S₂)

def Matrix.toLinearMap₂'Aux (f : Matrix n m N₂) : (n → R₁) →ₛₗ[σ₁] (m → R₂) →ₛₗ[σ₂] N₂ :=
  -- porting note: we don't seem to have `∑ i j` as valid notation yet
  mk₂'ₛₗ σ₁ σ₂ (fun (v : n → R₁) (w : m → R₂) => ∑ i, ∑ j, σ₂ (w j) • σ₁ (v i) • f i j)
    (fun _ _ _ => by simp only [Pi.add_apply, map_add, smul_add, sum_add_distrib, add_smul])
    (fun c v w => by
      simp only [Pi.smul_apply, smul_sum, smul_eq_mul, σ₁.map_mul, ← smul_comm _ (σ₁ c),
        SemigroupAction.mul_smul])
    (fun _ _ _ => by simp only [Pi.add_apply, map_add, add_smul, sum_add_distrib])
    (fun _ v w => by
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, SemigroupAction.mul_smul, smul_sum])

variable [DecidableEq n] [DecidableEq m]

theorem Matrix.toLinearMap₂'Aux_single (f : Matrix n m N₂) (i : n) (j : m) :
    f.toLinearMap₂'Aux σ₁ σ₂ (Pi.single i 1) (Pi.single j 1) = f i j := by
  rw [Matrix.toLinearMap₂'Aux, mk₂'ₛₗ_apply]
  have : (∑ i', ∑ j', (if i = i' then (1 : S₁) else (0 : S₁)) •
        (if j = j' then (1 : S₂) else (0 : S₂)) • f i' j') =
      f i j := by
    simp_rw [← Finset.smul_sum]
    simp only [ite_smul, one_smul, zero_smul, sum_ite_eq, mem_univ, ↓reduceIte]
  rw [← this]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by aesop

end AuxToLinearMap

section AuxToMatrix

section CommSemiring

variable [CommSemiring R] [Semiring R₁] [Semiring S₁] [Semiring R₂] [Semiring S₂]

variable [AddCommMonoid M₁] [Module R₁ M₁] [AddCommMonoid M₂] [Module R₂ M₂] [AddCommMonoid N₂]
  [Module R N₂] [Module S₁ N₂] [Module S₂ N₂] [SMulCommClass S₁ R N₂] [SMulCommClass S₂ R N₂]
  [SMulCommClass S₂ S₁ N₂]

variable {σ₁ : R₁ →+* S₁} {σ₂ : R₂ →+* S₂}

variable (R)

def LinearMap.toMatrix₂Aux (b₁ : n → M₁) (b₂ : m → M₂) :
    (M₁ →ₛₗ[σ₁] M₂ →ₛₗ[σ₂] N₂) →ₗ[R] Matrix n m N₂ where
  toFun f := of fun i j => f (b₁ i) (b₂ j)
  map_add' _f _g := rfl
  map_smul' _f _g := rfl
