/-
Extracted from LinearAlgebra/Span/TensorProduct.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The interaction of linear span and tensor product for mixed scalars.
-/

open Function TensorProduct

namespace Submodule

variable {R : Type*} (A : Type*) {M : Type*}

section CommSemiring

variable [CommSemiring R] [CommSemiring A] [Algebra R A]
  [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]
  (p : Submodule R M)

def tensorToSpan : A ⊗[R] p →ₗ[A] span A (p : Set M) :=
  AlgebraTensorModule.lift
    { toFun a := a • p.inclusionSpan A
      map_add' a b := add_smul a b _
      map_smul' a b := smul_assoc a b _ }
