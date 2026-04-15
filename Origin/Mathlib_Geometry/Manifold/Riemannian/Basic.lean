/-
Extracted from Geometry/Manifold/Riemannian/Basic.lean
Genuine: 6 of 8 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-! # Riemannian manifolds

A Riemannian manifold `M` is a real manifold such that its tangent spaces are endowed with an
inner product, depending smoothly on the point, and such that `M` has an emetric space
structure for which the distance is the infimum of lengths of paths.

We register a Prop-valued typeclass `IsRiemannianManifold I M` recording this fact, building on top
of `[EMetricSpace M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]`.

We show that an inner product vector space, with the associated canonical Riemannian metric,
satisfies the predicate `IsRiemannianManifold 𝓘(ℝ, E) E`.

In a general manifold with a Riemannian metric, we define the associated extended distance in the
manifold, and show that it defines the same topology as the pre-existing one. Therefore, one
may endow the manifold with an emetric space structure, see `EMetricSpace.ofRiemannianMetric`.
By definition, it then satisfies the predicate `IsRiemannianManifold I M`.

The following code block is the standard way to say "Let `M` be a `C^∞` Riemannian manifold".
```
open scoped Bundle
variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]
```
To register a `C^n` manifold for a general `n`, one should replace `[IsManifold I ∞ M]` with
`[IsManifold I n M] [IsManifold I 1 M]`, where the second one is needed to ensure that the
tangent bundle is well behaved (not necessary when `n` is concrete like 2 or 3 as there are
automatic instances for these cases). One can require whatever regularity one wants in the
`IsContMDiffRiemannianBundle` instance above, for example
`[IsContMDiffRiemannianBundle I n E (fun (x : M) ↦ TangentSpace I x)]`, and one should also add
`[IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]` (as above, Lean cannot infer
the latter from the former as it cannot guess `n`).
-/

open Bundle Bornology Set MeasureTheory Manifold Filter

open scoped ENNReal ContDiff Topology

local notation "⟪" x ", " y "⟫" => inner ℝ x y

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : WithTop ℕ∞}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable [PseudoEMetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

variable (I M) in

class IsRiemannianManifold : Prop where
  out (x y : M) : edist x y = riemannianEDist I x y

end

/-!
### Riemannian structure on an inner product vector space

We endow an inner product vector space with the canonical Riemannian metric, given by the
inner product of the vector space in each of the tangent spaces, and we show that this construction
satisfies the `IsRiemannianManifold 𝓘(ℝ, E) E` predicate, i.e., the extended distance between
two points is the infimum of the length of paths between these points.
-/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

set_option backward.isDefEq.respectTransparency false in

variable (F) in

noncomputable def riemannianMetricVectorSpace :
    ContMDiffRiemannianMetric 𝓘(ℝ, F) ω F (fun (x : F) ↦ TangentSpace 𝓘(ℝ, F) x) where
  inner x := (innerSL ℝ (E := F) : F →L[ℝ] F →L[ℝ] ℝ)
  symm x v w := real_inner_comm _ _
  pos x v hv := real_inner_self_pos.2 hv
  isVonNBounded x := by
    change IsVonNBounded ℝ {v : F | ⟪v, v⟫ < 1}
    have : Metric.ball (0 : F) 1 = {v : F | ⟪v, v⟫ < 1} := by
      ext v
      simp only [Metric.mem_ball, dist_zero_right, norm_eq_sqrt_re_inner (𝕜 := ℝ),
        RCLike.re_to_real, Set.mem_setOf_eq]
      conv_lhs => rw [show (1 : ℝ) = √1 by simp]
      rw [Real.sqrt_lt_sqrt_iff]
      exact real_inner_self_nonneg
    rw [← this]
    exact NormedSpace.isVonNBounded_ball ℝ F 1
  contMDiff := by
    intro x
    rw [contMDiffAt_section]
    convert contMDiffAt_const (c := innerSL ℝ)
    ext v w
    simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates, TangentSpace]

-- INSTANCE (free from Core): :

set_option backward.isDefEq.respectTransparency false in

lemma norm_tangentSpace_vectorSpace {x : F} {v : TangentSpace 𝓘(ℝ, F) x} :
    ‖v‖ = ‖letI V : F := v; V‖ := by
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner]

lemma nnnorm_tangentSpace_vectorSpace {x : F} {v : TangentSpace 𝓘(ℝ, F) x} :
    ‖v‖₊ = ‖letI V : F := v; V‖₊ := by
  simp [nnnorm, norm_tangentSpace_vectorSpace]

lemma enorm_tangentSpace_vectorSpace {x : F} {v : TangentSpace 𝓘(ℝ, F) x} :
    ‖v‖ₑ = ‖letI V : F := v; V‖ₑ := by
  simp [enorm, nnnorm_tangentSpace_vectorSpace]

open MeasureTheory Measure

lemma lintegral_fderiv_lineMap_eq_edist {x y : E} :
    ∫⁻ t in Icc 0 1, ‖fderivWithin ℝ (ContinuousAffineMap.lineMap (R := ℝ) x y) (Icc 0 1) t 1‖ₑ
      = edist x y := by
  have : edist x y = ∫⁻ t in Icc (0 : ℝ) 1, ‖y - x‖ₑ := by
    simp [edist_comm x y, edist_eq_enorm_sub]
  rw [this]
  apply setLIntegral_congr_fun measurableSet_Icc (fun z hz ↦ ?_)
  rw [show y - x = fderiv ℝ (ContinuousAffineMap.lineMap (R := ℝ) x y) z 1 by simp]
  congr
  exact fderivWithin_eq_fderiv (uniqueDiffOn_Icc zero_lt_one _ hz)
    (ContinuousAffineMap.differentiableAt _)

-- INSTANCE (free from Core): :

end

/-!
### Constructing a distance from a Riemannian structure

Let `M` be a real manifold with a Riemannian structure. We construct the associated distance and
show that the associated topology coincides with the pre-existing topology. Therefore, one may
endow `M` with an emetric space structure, called `EMetricSpace.ofRiemannianMetric`.
Moreover, we show that in this case the resulting emetric space satisfies the predicate
`IsRiemannianManifold I M`.

Showing that the distance topology coincides with the pre-existing topology is not trivial. The
two inclusions are proved respectively in `eventually_riemannianEDist_lt` and
`setOf_riemannianEDist_lt_subset_nhds`.

For the first one, we have to show that points which are close for the topology are at small
distance. For this, we use the path between the two points which is the pullback of the segment
in the extended chart, and argue that it is short because the images are close in the extended
chart.

For the second one, we have to show that any neighborhood of `x` contains all the points `y`
with `riemannianEDist x y < c` for some `c > 0`. For this, we argue that a short path from `x`
to `y` remains short in the extended chart, and therefore it doesn't have the time to exit
the image of the neighborhood in the extended chart.
-/

open Manifold Metric

open scoped NNReal

variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsManifold I 1 M] [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
