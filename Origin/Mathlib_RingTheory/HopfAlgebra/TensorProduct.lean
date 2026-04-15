/-
Extracted from RingTheory/HopfAlgebra/TensorProduct.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Tensor products of Hopf algebras

We define the Hopf algebra instance on the tensor product of two Hopf algebras.

-/

open Coalgebra TensorProduct HopfAlgebra

noncomputable abbrev HopfAlgebra.ofAlgHom {R A : Type*} [CommSemiring R] [CommSemiring A]
    [Bialgebra R A] (antipode : A →ₐ[R] A)
    (mul_antipode_rTensor_comul :
      ((Algebra.TensorProduct.lift antipode (.id R A) fun _ ↦ .all _).comp
        (Bialgebra.comulAlgHom R A)) = (Algebra.ofId R A).comp (Bialgebra.counitAlgHom R A))
    (mul_antipode_lTensor_comul :
      (Algebra.TensorProduct.lift (.id R A) antipode fun _ _ ↦ .all _ _).comp
        (Bialgebra.comulAlgHom R A) = (Algebra.ofId R A).comp (Bialgebra.counitAlgHom R A)) :
    HopfAlgebra R A where
  antipode := antipode
  mul_antipode_rTensor_comul := by
    rw [← Algebra.TensorProduct.lmul'_comp_map] at mul_antipode_rTensor_comul
    exact congr(($mul_antipode_rTensor_comul).toLinearMap)
  mul_antipode_lTensor_comul := by
    rw [← Algebra.TensorProduct.lmul'_comp_map] at mul_antipode_lTensor_comul
    exact congr(($mul_antipode_lTensor_comul).toLinearMap)

namespace TensorProduct

variable {R S A B : Type*} [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]
    [Algebra R S] [HopfAlgebra R A] [HopfAlgebra S B] [Algebra R B]
    [IsScalarTower R S B]

noncomputable

-- INSTANCE (free from Core): :
