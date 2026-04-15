/-
Extracted from RingTheory/TensorProduct/MonoidAlgebra.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Monoid algebras commute with base change

In this file we show that monoid algebras are stable under pushout.

## TODO

Additivise
-/

open Algebra TensorProduct

namespace MonoidAlgebra

variable {R M S A B : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring A] [CommSemiring B]

variable [Algebra R S] [Algebra R A] [Algebra R B] [CommMonoid M]

noncomputable def _root_.AddMonoidAlgebra.tensorEquiv.invFun [AddCommMonoid M] :
    AddMonoidAlgebra (A ⊗[R] B) M →ₐ[A] A ⊗[R] AddMonoidAlgebra B M :=
  AddMonoidAlgebra.liftNCAlgHom
    (Algebra.TensorProduct.map (.id _ _) AddMonoidAlgebra.singleZeroAlgHom)
    (Algebra.TensorProduct.includeRight.toMonoidHom.comp <| AddMonoidAlgebra.of B M)
      fun _ _ ↦ .all ..
