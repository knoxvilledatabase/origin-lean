/-
Extracted from Algebra/Lie/BaseChange.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Extension and restriction of scalars for Lie algebras and Lie modules

Lie algebras and their representations have a well-behaved theory of extension and restriction of
scalars.

## Main definitions

* `LieAlgebra.ExtendScalars.instLieAlgebra`
* `LieAlgebra.ExtendScalars.instLieModule`
* `LieAlgebra.RestrictScalars.lieAlgebra`

## Tags

lie ring, lie algebra, extension of scalars, restriction of scalars, base change
-/

open scoped TensorProduct

variable (R A L M : Type*)

namespace LieAlgebra

namespace ExtendScalars

variable [CommRing R] [CommRing A] [Algebra R A] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

set_option backward.privateInPublic true in

private def bracket' : A ⊗[R] L →ₗ[A] A ⊗[R] M →ₗ[A] A ⊗[R] M :=
  TensorProduct.curry <|
    TensorProduct.AlgebraTensorModule.map
        (LinearMap.mul' A A) (LieModule.toModuleHom R L M : L ⊗[R] M →ₗ[R] M) ∘ₗ
      (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R R A A A L A M).toLinearMap
