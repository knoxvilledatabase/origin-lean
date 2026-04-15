/-
Extracted from RingTheory/GradedAlgebra/Basic.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Internally-graded rings and algebras

This file defines the typeclass `GradedAlgebra 𝒜`, for working with an algebra `A` that is
internally graded by a collection of submodules `𝒜 : ι → Submodule R A`.
See the docstring of that typeclass for more information.

## Main definitions

* `GradedRing 𝒜`: the typeclass, which is a combination of `SetLike.GradedMonoid`, and
  `DirectSum.Decomposition 𝒜`.
* `GradedAlgebra 𝒜`: A convenience alias for `GradedRing` when `𝒜` is a family of submodules.
* `DirectSum.decomposeRingEquiv 𝒜 : A ≃ₐ[R] ⨁ i, 𝒜 i`, a more bundled version of
  `DirectSum.decompose 𝒜`.
* `DirectSum.decomposeAlgEquiv 𝒜 : A ≃ₐ[R] ⨁ i, 𝒜 i`, a more bundled version of
  `DirectSum.decompose 𝒜`.
* `GradedAlgebra.proj 𝒜 i` is the linear map from `A` to its degree `i : ι` component, such that
  `proj 𝒜 i x = decompose 𝒜 x i`.

## Implementation notes

For now, we do not have internally-graded semirings and internally-graded rings; these can be
represented with `𝒜 : ι → Submodule ℕ A` and `𝒜 : ι → Submodule ℤ A` respectively, since all
`Semiring`s are ℕ-algebras via `Semiring.toNatAlgebra`, and all `Ring`s are `ℤ`-algebras via
`Ring.toIntAlgebra`.

## Tags

graded algebra, graded ring, graded semiring, decomposition
-/

open DirectSum

variable {ι R A σ : Type*}

section GradedRing

variable [DecidableEq ι] [AddMonoid ι] [CommSemiring R] [Semiring A] [Algebra R A]

variable [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ)

open DirectSum

class GradedRing (𝒜 : ι → σ) extends SetLike.GradedMonoid 𝒜, DirectSum.Decomposition 𝒜

variable [GradedRing 𝒜]

namespace DirectSum

def decomposeRingEquiv : A ≃+* ⨁ i, 𝒜 i :=
  RingEquiv.symm
    { (decomposeAddEquiv 𝒜).symm with
      map_mul' := (coeRingHom 𝒜).map_mul }
