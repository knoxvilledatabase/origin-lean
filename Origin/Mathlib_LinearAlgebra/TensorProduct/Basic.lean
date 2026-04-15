/-
Extracted from LinearAlgebra/TensorProduct/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Universal property of the tensor product

Given any bilinear map `f : M →ₛₗ[σ₁₂] N →ₛₗ[σ₁₂] P₂`, there is a unique semilinear map
`TensorProduct.lift f : TensorProduct R M N →ₛₗ[σ₁₂] P₂` whose composition with the canonical
bilinear map `TensorProduct.mk` is the given bilinear map `f`.  Uniqueness is shown in the theorem
`TensorProduct.lift.unique`.

## Tags

bilinear, tensor, tensor product
-/

section Semiring

variable {R R₂ R₃ R' R'' : Type*}

variable [CommSemiring R] [CommSemiring R₂] [CommSemiring R₃] [Monoid R'] [Semiring R'']

variable {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃}

variable {A M N P Q S : Type*}

variable {M₂ M₃ N₂ N₃ P' P₂ P₃ Q' Q₂ Q₃ : Type*}

variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q] [AddCommMonoid S]

variable [AddCommMonoid P'] [AddCommMonoid Q']

variable [AddCommMonoid M₂] [AddCommMonoid N₂] [AddCommMonoid P₂] [AddCommMonoid Q₂]

variable [AddCommMonoid M₃] [AddCommMonoid N₃] [AddCommMonoid P₃] [AddCommMonoid Q₃]

variable [DistribMulAction R' M]

variable [Module R'' M]

variable [Module R M] [Module R N] [Module R S]

variable [Module R P'] [Module R Q']

variable [Module R₂ M₂] [Module R₂ N₂] [Module R₂ P₂] [Module R₂ Q₂]

variable [Module R₃ M₃] [Module R₃ N₃] [Module R₃ P₃] [Module R₃ Q₃]

variable (M N)

namespace TensorProduct

section Module

variable {M N}

def liftAddHom (f : M →+ N →+ P)
    (hf : ∀ (r : R) (m : M) (n : N), f (r • m) n = f m (r • n)) :
    M ⊗[R] N →+ P :=
  (addConGen (TensorProduct.Eqv R M N)).lift (FreeAddMonoid.lift (fun mn : M × N => f mn.1 mn.2)) <|
    AddCon.addConGen_le fun x y hxy =>
      match x, y, hxy with
      | _, _, .of_zero_left n =>
        (AddCon.ker_rel _).2 <| by simp_rw [map_zero, FreeAddMonoid.lift_eval_of, map_zero,
          AddMonoidHom.zero_apply]
      | _, _, .of_zero_right m =>
        (AddCon.ker_rel _).2 <| by simp_rw [map_zero, FreeAddMonoid.lift_eval_of, map_zero]
      | _, _, .of_add_left m₁ m₂ n =>
        (AddCon.ker_rel _).2 <| by simp_rw [map_add, FreeAddMonoid.lift_eval_of, map_add,
          AddMonoidHom.add_apply]
      | _, _, .of_add_right m n₁ n₂ =>
        (AddCon.ker_rel _).2 <| by simp_rw [map_add, FreeAddMonoid.lift_eval_of, map_add]
      | _, _, .of_smul s m n =>
        (AddCon.ker_rel _).2 <| by rw [FreeAddMonoid.lift_eval_of, FreeAddMonoid.lift_eval_of, hf]
      | _, _, .add_comm x y =>
        (AddCon.ker_rel _).2 <| by simp_rw [map_add, add_comm]
