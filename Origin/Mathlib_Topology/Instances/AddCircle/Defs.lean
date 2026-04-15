/-
Extracted from Topology/Instances/AddCircle/Defs.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The additive circle

We define the additive circle `AddCircle p` as the quotient `𝕜 ⧸ ℤ ∙ p` for some period `p : 𝕜`.

See also `Circle` and `Real.Angle`.  For the normed group structure on `AddCircle`, see
`AddCircle.NormedAddCommGroup` in a later file.

## Main definitions and results:

* `AddCircle`: the additive circle `𝕜 ⧸ ℤ ∙ p` for some period `p : 𝕜`
* `UnitAddCircle`: the special case `ℝ ⧸ ℤ`
* `AddCircle.equivAddCircle`: the rescaling equivalence `AddCircle p ≃+ AddCircle q`
* `AddCircle.equivIco` and `AddCircle.equivIoc`: the natural equivalences
  `AddCircle p ≃ Ico a (a + p)` and `AddCircle p ≃ Ioc a (a + p)`
* `AddCircle.addOrderOf_div_of_gcd_eq_one`: rational points have finite order
* `AddCircle.exists_gcd_eq_one_of_isOfFinAddOrder`: finite-order points are rational
* `AddCircle.homeoIccQuot`: the natural topological equivalence between `AddCircle p` and
  `Icc a (a + p)` with its endpoints identified.
* `AddCircle.liftIco_continuous` and `AddCircle.liftIoc_continuous`: if `f : ℝ → B` is continuous,
  and `f a = f (a + p)` for some `a`, then there is a continuous function `AddCircle p → B`
  which agrees with `f` on `Icc a (a + p)`.

## Implementation notes:

Although the most important case is `𝕜 = ℝ` we wish to support other types of scalars, such as
the rational circle `AddCircle (1 : ℚ)`, and so we set things up more generally.

## TODO

* Link with periodicity
* Lie group structure
* Exponential equivalence to `Circle`

-/

noncomputable section

open AddCommGroup Set Function AddSubgroup TopologicalSpace

open Topology

variable {𝕜 B : Type*}

section Continuity

variable [AddCommGroup 𝕜] [LinearOrder 𝕜] [IsOrderedAddMonoid 𝕜] [Archimedean 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  {p : 𝕜} (hp : 0 < p) (a x : 𝕜)

theorem eventuallyEq_toIcoDiv_nhdsGE : toIcoDiv hp a =ᶠ[𝓝[≥] x] fun _ ↦ toIcoDiv hp a x := by
  simp only [Filter.EventuallyEq, toIcoDiv_eq_iff, sub_mem_Ico_iff_left]
  apply Ico_mem_nhdsGE_of_mem
  rw [← sub_mem_Ico_iff_left, ← toIcoDiv_eq_iff]

theorem continuousWithinAt_toIcoDiv_Ici : ContinuousWithinAt (toIcoDiv hp a) (Ici x) x :=
  Filter.tendsto_pure.mpr (eventuallyEq_toIcoDiv_nhdsGE hp a x) |>.mono_right <| pure_le_nhds _

theorem eventuallyEq_toIocDiv_nhdsLE : toIocDiv hp a =ᶠ[𝓝[≤] x] fun _ ↦ toIocDiv hp a x := by
  simp only [Filter.EventuallyEq, toIocDiv_eq_iff, sub_mem_Ioc_iff_left]
  apply Ioc_mem_nhdsLE_of_mem
  rw [← sub_mem_Ioc_iff_left, ← toIocDiv_eq_iff]

theorem continuousWithinAt_toIocDiv_Iic : ContinuousWithinAt (toIocDiv hp a) (Iic x) x :=
  Filter.tendsto_pure.mpr (eventuallyEq_toIocDiv_nhdsLE hp a x) |>.mono_right <| pure_le_nhds _

theorem continuousWithinAt_toIcoMod_Ici : ContinuousWithinAt (toIcoMod hp a) (Ici x) x :=
  continuousWithinAt_id.sub <|
    (continuousWithinAt_toIcoDiv_Ici hp a x).smul continuousWithinAt_const
