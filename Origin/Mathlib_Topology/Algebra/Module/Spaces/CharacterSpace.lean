/-
Extracted from Topology/Algebra/Module/Spaces/CharacterSpace.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Character space of a topological algebra

The character space of a topological algebra is the subset of elements of the weak dual that
are also algebra homomorphisms. This space is used in the Gelfand transform, which gives an
isomorphism between a commutative C⋆-algebra and continuous functions on the character space
of the algebra. This, in turn, is used to construct the continuous functional calculus on
C⋆-algebras.


## Implementation notes

We define `WeakDual.characterSpace 𝕜 A` as a subset of the weak dual, which automatically puts the
correct topology on the space. We then define `WeakDual.CharacterSpace.toAlgHom` which provides the
algebra homomorphism corresponding to any element. We also provide `WeakDual.CharacterSpace.toCLM`
which provides the element as a continuous linear map. (Even though `WeakDual 𝕜 A` is a type copy of
`A →L[𝕜] 𝕜`, this is often more convenient.)

## Tags

character space, Gelfand transform, functional calculus

-/

namespace WeakDual

def characterSpace (𝕜 : Type*) (A : Type*) [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
    [ContinuousConstSMul 𝕜 𝕜] [NonUnitalNonAssocSemiring A] [TopologicalSpace A] [Module 𝕜 A] :=
  {φ : WeakDual 𝕜 A | φ ≠ 0 ∧ ∀ x y : A, φ (x * y) = φ x * φ y}

variable {𝕜 : Type*} {A : Type*}

namespace CharacterSpace

section NonUnitalNonAssocSemiring

variable [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜] [ContinuousConstSMul 𝕜 𝕜]
  [NonUnitalNonAssocSemiring A] [TopologicalSpace A] [Module 𝕜 A]

-- INSTANCE (free from Core): instFunLike

-- INSTANCE (free from Core): instContinuousLinearMapClass
