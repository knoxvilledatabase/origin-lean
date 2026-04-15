/-
Extracted from LinearAlgebra/SymmetricAlgebra/Basic.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Symmetric Algebras

Given a commutative semiring `R`, and an `R`-module `M`, we construct the symmetric algebra of `M`.
This is the free commutative `R`-algebra generated (`R`-linearly) by the module `M`.

## Notation

* `SymmetricAlgebra R M`: a concrete construction of the symmetric algebra defined as a
  quotient of the tensor algebra. It is endowed with an R-algebra structure and a commutative
  ring structure.
* `SymmetricAlgebra.ι R`: the canonical R-linear map `M →ₗ[R] SymmetricAlgebra R M`.
* Given a morphism `ι : M →ₗ[R] A`, `IsSymmetricAlgebra ι` is a proposition saying that the algebra
  homomorphism from `SymmetricAlgebra R M` to `A` lifted from `ι` is bijective.
* Given a linear map `f : M →ₗ[R] A'` to a commutative R-algebra `A'`, and a morphism
  `ι : M →ₗ[R] A` with `p : IsSymmetricAlgebra ι`, `IsSymmetricAlgebra.lift p f`
  is the lift of `f` to an `R`-algebra morphism `A →ₐ[R] A'`.

## Note

See `SymAlg R` instead if you are looking for the symmetrized algebra, which gives a commutative
multiplication on `R` by $a \circ b = \frac{1}{2}(ab + ba)$.
-/

variable (R M : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M]

inductive TensorAlgebra.SymRel : TensorAlgebra R M → TensorAlgebra R M → Prop where
  | mul_comm (x y : M) : SymRel (ι R x * ι R y) (ι R y * ι R x)

open TensorAlgebra

abbrev SymmetricAlgebra := RingQuot (SymRel R M)

namespace SymmetricAlgebra

abbrev algHom : TensorAlgebra R M →ₐ[R] SymmetricAlgebra R M := RingQuot.mkAlgHom R (SymRel R M)

lemma algHom_surjective : Function.Surjective (algHom R M) :=
  RingQuot.mkAlgHom_surjective _ _

def ι : M →ₗ[R] SymmetricAlgebra R M := algHom R M ∘ₗ TensorAlgebra.ι R
