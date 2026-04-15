/-
Extracted from Geometry/Manifold/Algebra/LieGroup.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Lie groups

A Lie group is a group that is also a `C^n` manifold, in which the group operations of
multiplication and inversion are `C^n` maps. Regularity of the group multiplication means that
multiplication is a `C^n` mapping of the product manifold `G` × `G` into `G`.

Note that, since a manifold here is not second-countable and Hausdorff, a Lie group here is not
guaranteed to be second-countable (even though it can be proved that it is Hausdorff). Note also
that Lie groups here are not necessarily finite dimensional.

## Main definitions

* `LieAddGroup I G` : a Lie additive group where `G` is a manifold on the model with corners `I`.
* `LieGroup I G` : a Lie multiplicative group where `G` is a manifold on the model with corners `I`.
* `ContMDiffInv₀`: typeclass for `C^n` manifolds with `0` and `Inv` such that inversion is `C^n`
  map at each non-zero point. This includes complete normed fields and (multiplicative) Lie groups.


## Main results
* `ContMDiff.inv`, `ContMDiff.div` and variants: point-wise inversion and division of maps `M → G`
  is `C^n`.
* `ContMDiff.inv₀` and variants: if `ContMDiffInv₀ I n N`, point-wise inversion of `C^n`
  maps `f : M → N` is `C^n` at all points at which `f` doesn't vanish.
* `ContMDiff.div₀` and variants: if also `ContMDiffMul I n N` (i.e., `N` is a Lie group except
  possibly for smoothness of inversion at `0`), similar results hold for point-wise division.
* `instNormedSpaceLieAddGroup` : a normed vector space over a nontrivially normed field
  is an additive Lie group.
* `Instances/UnitsOfNormedAlgebra` shows that the group of units of a complete normed `𝕜`-algebra
  is a multiplicative Lie group.

## Implementation notes

A priori, a Lie group here is a manifold with corners.

The definition of Lie group cannot require `I : ModelWithCorners 𝕜 E E` with the same space as the
model space and as the model vector space, as one might hope, because in the product situation,
the model space is `ModelProd E E'` and the model vector space is `E × E'`, which are not the same,
so the definition does not apply. Hence the definition should be more general, allowing
`I : ModelWithCorners 𝕜 E H`.
-/

noncomputable section

open scoped Manifold ContDiff

class LieAddGroup {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] (I : ModelWithCorners 𝕜 E H)
    (n : WithTop ℕ∞) (G : Type*)
    [AddGroup G] [TopologicalSpace G] [ChartedSpace H G] : Prop extends ContMDiffAdd I n G where
  /-- Negation is smooth in an additive Lie group. -/
  contMDiff_neg : CMDiff n fun a : G ↦ -a
