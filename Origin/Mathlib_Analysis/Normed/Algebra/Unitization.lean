/-
Extracted from Analysis/Normed/Algebra/Unitization.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Unitization norms

Given a not-necessarily-unital normed `𝕜`-algebra `A`, it is frequently of interest to equip its
`Unitization` with a norm which simultaneously makes it into a normed algebra and also satisfies
two properties:

- `‖1‖ = 1` (i.e., `NormOneClass`)
- The embedding of `A` in `Unitization 𝕜 A` is an isometry. (i.e., `Isometry Unitization.inr`)

One way to do this is to pull back the norm from `WithLp 1 (𝕜 × A)`, that is,
`‖(k, a)‖ = ‖k‖ + ‖a‖` using `Unitization.addEquiv` (i.e., the identity map).
This is implemented for the type synonym `WithLp 1 (Unitization 𝕜 A)` in
`WithLp.instUnitizationNormedAddCommGroup`, and it is shown there that this is a Banach algebra.
However, when the norm on `A` is *regular* (i.e., `ContinuousLinearMap.mul` is an isometry), there
is another natural choice: the pullback of the norm on `𝕜 × (A →L[𝕜] A)` under the map
`(k, a) ↦ (k, k • 1 + ContinuousLinearMap.mul 𝕜 A a)`. It turns out that among all norms on the
unitization satisfying the properties specified above, the norm inherited from
`WithLp 1 (𝕜 × A)` is maximal, and the norm inherited from this pullback is minimal.
Of course, this means that `WithLp.equiv : WithLp 1 (Unitization 𝕜 A) → Unitization 𝕜 A` can be
upgraded to a continuous linear equivalence (when `𝕜` and `A` are complete).

structure on `Unitization 𝕜 A` using the pullback described above. The reason for choosing this norm
is that for a C⋆-algebra `A` its norm is always regular, and the pullback norm on `Unitization 𝕜 A`
is then also a C⋆-norm.

## Main definitions

- `Unitization.splitMul : Unitization 𝕜 A →ₐ[𝕜] (𝕜 × (A →L[𝕜] A))`: The first coordinate of this
  map is just `Unitization.fst` and the second is the `Unitization.lift` of the left regular
  representation of `A` (i.e., `NonUnitalAlgHom.Lmul`). We use this map to pull back the
  `NormedRing` and `NormedAlgebra` structures.

## Main statements

- `Unitization.instNormedRing`, `Unitization.instNormedAlgebra`, `Unitization.instNormOneClass`,
  `Unitization.instCompleteSpace`: when `A` is a non-unital Banach `𝕜`-algebra with a regular norm,
  then `Unitization 𝕜 A` is a unital Banach `𝕜`-algebra with `‖1‖ = 1`.
- `Unitization.norm_inr`, `Unitization.isometry_inr`: the natural inclusion `A → Unitization 𝕜 A`
  is an isometry, or in mathematical parlance, the norm on `A` extends to a norm on
  `Unitization 𝕜 A`.

## Implementation details

We ensure that the uniform structure, and hence also the topological structure, is definitionally
equal to the pullback of `instUniformSpaceProd` along `Unitization.addEquiv` (this is essentially
viewing `Unitization 𝕜 A` as `𝕜 × A`) by means of forgetful inheritance. The same is true of the
bornology.

-/

suppress_compilation

variable (𝕜 A : Type*) [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A]

variable [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]

open ContinuousLinearMap

namespace Unitization

def splitMul : Unitization 𝕜 A →ₐ[𝕜] 𝕜 × (A →L[𝕜] A) :=
  (lift 0).prod (lift <| NonUnitalAlgHom.Lmul 𝕜 A)

variable {𝕜 A}
