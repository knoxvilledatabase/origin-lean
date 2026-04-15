/-
Extracted from Geometry/Manifold/Algebra/LieGroup.lean
Genuine: 14 of 28 | Dissolved: 10 | Infrastructure: 4
-/
import Origin.Core
import Mathlib.Geometry.Manifold.Algebra.Monoid

/-!
# Lie groups

A Lie group is a group that is also a smooth manifold, in which the group operations of
multiplication and inversion are smooth maps. Smoothness of the group multiplication means that
multiplication is a smooth mapping of the product manifold `G` × `G` into `G`.

Note that, since a manifold here is not second-countable and Hausdorff a Lie group here is not
guaranteed to be second-countable (even though it can be proved it is Hausdorff). Note also that Lie
groups here are not necessarily finite dimensional.

## Main definitions

* `LieAddGroup I G` : a Lie additive group where `G` is a manifold on the model with corners `I`.
* `LieGroup I G` : a Lie multiplicative group where `G` is a manifold on the model with corners `I`.
* `SmoothInv₀`: typeclass for smooth manifolds with `0` and `Inv` such that inversion is a smooth
  map at each non-zero point. This includes complete normed fields and (multiplicative) Lie groups.


## Main results
* `ContMDiff.inv`, `ContMDiff.div` and variants: point-wise inversion and division of maps `M → G`
  is smooth
* `ContMDiff.inv₀` and variants: if `SmoothInv₀ N`, point-wise inversion of smooth maps `f : M → N`
  is smooth at all points at which `f` doesn't vanish.
* `ContMDiff.div₀` and variants: if also `SmoothMul N` (i.e., `N` is a Lie group except possibly
  for smoothness of inversion at `0`), similar results hold for point-wise division.
* `normedSpaceLieAddGroup` : a normed vector space over a nontrivially normed field
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

open scoped Manifold

class LieAddGroup {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] (I : ModelWithCorners 𝕜 E H) (G : Type*)
    [AddGroup G] [TopologicalSpace G] [ChartedSpace H G] extends SmoothAdd I G : Prop where
  /-- Negation is smooth in an additive Lie group. -/
  smooth_neg : ContMDiff I I ⊤ fun a : G => -a

@[to_additive]
class LieGroup {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] (I : ModelWithCorners 𝕜 E H) (G : Type*)
    [Group G] [TopologicalSpace G] [ChartedSpace H G] extends SmoothMul I G : Prop where
  /-- Inversion is smooth in a Lie group. -/
  smooth_inv : ContMDiff I I ⊤ fun a : G => a⁻¹

/-!
  ### Smoothness of inversion, negation, division and subtraction

  Let `f : M → G` be a `C^n` or smooth functions into a Lie group, then `f` is point-wise
  invertible with smooth inverse `f`. If `f` and `g` are two such functions, the quotient
  `f / g` (i.e., the point-wise product of `f` and the point-wise inverse of `g`) is also smooth. -/

section PointwiseDivision

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {G : Type*}
  [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I G] {E' : Type*}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]
  {n : ℕ∞}

section

variable (I)

@[to_additive "In an additive Lie group, inversion is a smooth map."]
theorem contMDiff_inv : ContMDiff I I ⊤ fun x : G => x⁻¹ :=
  LieGroup.smooth_inv

include I in

@[to_additive "An additive Lie group is an additive topological group. This is not an instance for

technical reasons, see note [Design choices about smooth algebraic structures]."]

theorem topologicalGroup_of_lieGroup : TopologicalGroup G :=
  { continuousMul_of_smooth I with continuous_inv := (contMDiff_inv I).continuous }

end

@[to_additive]
theorem ContMDiffWithinAt.inv {f : M → G} {s : Set M} {x₀ : M}
    (hf : ContMDiffWithinAt I' I n f s x₀) : ContMDiffWithinAt I' I n (fun x => (f x)⁻¹) s x₀ :=
  ((contMDiff_inv I).of_le le_top).contMDiffAt.contMDiffWithinAt.comp x₀ hf <| Set.mapsTo_univ _ _

@[to_additive]
theorem ContMDiffAt.inv {f : M → G} {x₀ : M} (hf : ContMDiffAt I' I n f x₀) :
    ContMDiffAt I' I n (fun x => (f x)⁻¹) x₀ :=
  ((contMDiff_inv I).of_le le_top).contMDiffAt.comp x₀ hf

@[to_additive]
theorem ContMDiffOn.inv {f : M → G} {s : Set M} (hf : ContMDiffOn I' I n f s) :
    ContMDiffOn I' I n (fun x => (f x)⁻¹) s := fun x hx => (hf x hx).inv

@[to_additive]
theorem ContMDiff.inv {f : M → G} (hf : ContMDiff I' I n f) : ContMDiff I' I n fun x => (f x)⁻¹ :=
  fun x => (hf x).inv

@[to_additive]
theorem ContMDiffWithinAt.div {f g : M → G} {s : Set M} {x₀ : M}
    (hf : ContMDiffWithinAt I' I n f s x₀) (hg : ContMDiffWithinAt I' I n g s x₀) :
    ContMDiffWithinAt I' I n (fun x => f x / g x) s x₀ := by
  simp_rw [div_eq_mul_inv]; exact hf.mul hg.inv

@[to_additive]
theorem ContMDiffAt.div {f g : M → G} {x₀ : M} (hf : ContMDiffAt I' I n f x₀)
    (hg : ContMDiffAt I' I n g x₀) : ContMDiffAt I' I n (fun x => f x / g x) x₀ := by
  simp_rw [div_eq_mul_inv]; exact hf.mul hg.inv

@[to_additive]
theorem ContMDiffOn.div {f g : M → G} {s : Set M} (hf : ContMDiffOn I' I n f s)
    (hg : ContMDiffOn I' I n g s) : ContMDiffOn I' I n (fun x => f x / g x) s := by
  simp_rw [div_eq_mul_inv]; exact hf.mul hg.inv

@[to_additive]
theorem ContMDiff.div {f g : M → G} (hf : ContMDiff I' I n f) (hg : ContMDiff I' I n g) :
    ContMDiff I' I n fun x => f x / g x := by simp_rw [div_eq_mul_inv]; exact hf.mul hg.inv

end PointwiseDivision

/-! Binary product of Lie groups -/

section Product

@[to_additive]
instance {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {G : Type*}
    [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I G] {E' : Type*}
    [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
    {I' : ModelWithCorners 𝕜 E' H'} {G' : Type*} [TopologicalSpace G'] [ChartedSpace H' G']
    [Group G'] [LieGroup I' G'] : LieGroup (I.prod I') (G × G') :=
  { SmoothMul.prod _ _ _ _ with smooth_inv := contMDiff_fst.inv.prod_mk contMDiff_snd.inv }

end Product

/-! ### Normed spaces are Lie groups -/

instance normedSpaceLieAddGroup {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] : LieAddGroup 𝓘(𝕜, E) E where
  smooth_neg := contDiff_neg.contMDiff

/-! ## Smooth manifolds with smooth inversion away from zero

Typeclass for smooth manifolds with `0` and `Inv` such that inversion is smooth at all non-zero
points. (This includes multiplicative Lie groups, but also complete normed semifields.)
Point-wise inversion is smooth when the function/denominator is non-zero. -/

section SmoothInv₀

-- DISSOLVED: SmoothInv₀

instance {𝕜 : Type*} [NontriviallyNormedField 𝕜] : SmoothInv₀ 𝓘(𝕜) 𝕜 where
  smoothAt_inv₀ x hx := by
    change ContMDiffAt 𝓘(𝕜) 𝓘(𝕜) ⊤ Inv.inv x
    rw [contMDiffAt_iff_contDiffAt]
    exact contDiffAt_inv 𝕜 hx

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] (I : ModelWithCorners 𝕜 E H) {G : Type*}
  [TopologicalSpace G] [ChartedSpace H G] [Inv G] [Zero G] [SmoothInv₀ I G] {E' : Type*}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]
  {n : ℕ∞} {f : M → G}

-- DISSOLVED: contMDiffAt_inv₀

include I in

theorem hasContinuousInv₀_of_hasSmoothInv₀ : HasContinuousInv₀ G :=
  { continuousAt_inv₀ := fun _ hx ↦ (contMDiffAt_inv₀ I hx).continuousAt }

theorem contMDiffOn_inv₀ : ContMDiffOn I I ⊤ (Inv.inv : G → G) {0}ᶜ := fun _x hx =>
  (contMDiffAt_inv₀ I hx).contMDiffWithinAt

variable {I} {s : Set M} {a : M}

-- DISSOLVED: ContMDiffWithinAt.inv₀

-- DISSOLVED: ContMDiffAt.inv₀

-- DISSOLVED: ContMDiff.inv₀

-- DISSOLVED: ContMDiffOn.inv₀

end SmoothInv₀

/-! ### Point-wise division of smooth functions

If `[SmoothMul I N]` and `[SmoothInv₀ I N]`, point-wise division of smooth functions `f : M → N`
is smooth whenever the denominator is non-zero. (This includes `N` being a completely normed field.)
-/

section Div

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {G : Type*}
  [TopologicalSpace G] [ChartedSpace H G] [GroupWithZero G] [SmoothInv₀ I G] [SmoothMul I G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]
  {f g : M → G} {s : Set M} {a : M} {n : ℕ∞}

-- DISSOLVED: ContMDiffWithinAt.div₀

-- DISSOLVED: ContMDiffOn.div₀

-- DISSOLVED: ContMDiffAt.div₀

-- DISSOLVED: ContMDiff.div₀

end Div
