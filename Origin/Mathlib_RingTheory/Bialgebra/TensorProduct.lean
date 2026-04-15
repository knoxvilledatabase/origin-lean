/-
Extracted from RingTheory/Bialgebra/TensorProduct.lean
Genuine: 1 of 6 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-!
# Tensor products of bialgebras

We define the data in the monoidal structure on the category of bialgebras - e.g. the bialgebra
instance on a tensor product of bialgebras, and the tensor product of two `BialgHom`s as a
`BialgHom`. This is done by combining the corresponding API for coalgebras and algebras.

-/

open scoped TensorProduct

namespace Bialgebra.TensorProduct

open Coalgebra.TensorProduct

variable (R S A B C D : Type*) [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]
  [Bialgebra S A] [Bialgebra R B] [Algebra R A] [Algebra R S] [IsScalarTower R S A]

-- INSTANCE (free from Core): _root_.TensorProduct.instBialgebra

variable {R S A B C D}

variable [Semiring C] [Semiring D] [Bialgebra S C]
  [Bialgebra R D] [Algebra R C] [IsScalarTower R S C]

noncomputable def map (f : A →ₐc[S] C) (g : B →ₐc[R] D) :
    A ⊗[R] B →ₐc[S] C ⊗[R] D :=
  { Coalgebra.TensorProduct.map (f : A →ₗc[S] C) (g : B →ₗc[R] D),
    Algebra.TensorProduct.map (f : A →ₐ[S] C) (g : B →ₐ[R] D) with }
