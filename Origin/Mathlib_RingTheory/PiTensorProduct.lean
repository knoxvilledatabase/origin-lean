/-
Extracted from RingTheory/PiTensorProduct.lean
Genuine: 1 of 4 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Tensor product of `R`-algebras and rings

If `(Aᵢ)` is a family of `R`-algebras then the `R`-tensor product `⨂ᵢ Aᵢ` is an `R`-algebra as well
with structure map defined by `r ↦ r • 1`.

In particular if we take `R` to be `ℤ`, then this collapses into the tensor product of rings.
-/

open TensorProduct Function

variable {ι R' R : Type*} {A : ι → Type*}

namespace PiTensorProduct

noncomputable section AddCommMonoidWithOne

variable [CommSemiring R] [∀ i, AddCommMonoidWithOne (A i)] [∀ i, Module R (A i)]

-- INSTANCE (free from Core): instOne

-- INSTANCE (free from Core): instAddCommMonoidWithOne

end AddCommMonoidWithOne

noncomputable section NonUnitalNonAssocSemiring

variable [CommSemiring R] [∀ i, NonUnitalNonAssocSemiring (A i)]

variable [∀ i, Module R (A i)] [∀ i, SMulCommClass R (A i) (A i)] [∀ i, IsScalarTower R (A i) (A i)]

attribute [aesop safe] mul_add mul_smul_comm smul_mul_assoc add_mul in

def mul : (⨂[R] i, A i) →ₗ[R] (⨂[R] i, A i) →ₗ[R] (⨂[R] i, A i) :=
  PiTensorProduct.piTensorHomMap₂ <| tprod R fun _ ↦ LinearMap.mul _ _
