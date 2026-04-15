/-
Extracted from Analysis/BoxIntegral/Basic.lean
Genuine: 6 of 6 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Integrals of Riemann, Henstock-Kurzweil, and McShane

In this file we define the integral of a function over a box in `ℝⁿ`. The same definition works for
Riemann, Henstock-Kurzweil, and McShane integrals.

As usual, we represent `ℝⁿ` as the type of functions `ι → ℝ` for some finite type `ι`. A rectangular
box `(l, u]` in `ℝⁿ` is defined to be the set `{x : ι → ℝ | ∀ i, l i < x i ∧ x i ≤ u i}`, see
`BoxIntegral.Box`.

Let `vol` be a box-additive function on boxes in `ℝⁿ` with codomain `E →L[ℝ] F`. Given a function
`f : ℝⁿ → E`, a box `I` and a tagged partition `π` of this box, the *integral sum* of `f` over `π`
with respect to the volume `vol` is the sum of `vol J (f (π.tag J))` over all boxes of `π`. Here
`π.tag J` is the point (tag) in `ℝⁿ` associated with the box `J`.

The integral is defined as the limit of integral sums along a filter. Different filters correspond
to different integration theories. In order to avoid code duplication, all our definitions and
theorems take an argument `l : BoxIntegral.IntegrationParams`. This is a type that holds three
Boolean values, and encodes eight filters including those corresponding to Riemann,
Henstock-Kurzweil, and McShane integrals.

Following the design of infinite sums (see `hasSum` and `tsum`), we define a predicate
`BoxIntegral.HasIntegral` and a function `BoxIntegral.integral` that returns a vector satisfying
the predicate or zero if the function is not integrable.

Then we prove some basic properties of box integrals (linearity, a formula for the integral of a
constant). We also prove a version of the Henstock-Sacks inequality (see
`BoxIntegral.Integrable.dist_integralSum_le_of_memBaseSet` and
`BoxIntegral.Integrable.dist_integralSum_sum_integral_le_of_memBaseSet_of_iUnion_eq`), prove
integrability of continuous functions, and provide a criterion for integrability w.r.t. a
non-Riemann filter (e.g., Henstock-Kurzweil and McShane).

## Notation

- `ℝⁿ`: local notation for `ι → ℝ`

## Tags

integral
-/

open scoped Topology NNReal Filter Uniformity BoxIntegral

open Set Finset Function Filter Metric BoxIntegral.IntegrationParams

noncomputable section

namespace BoxIntegral

universe u v w

variable {ι : Type u} {E : Type v} {F : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {I J : Box ι} {π : TaggedPrepartition I}

open TaggedPrepartition

local notation "ℝⁿ" => ι → ℝ

/-!
### Integral sum and its basic properties
-/

def integralSum (f : ℝⁿ → E) (vol : ι →ᵇᵃ E →L[ℝ] F) (π : TaggedPrepartition I) : F :=
  ∑ J ∈ π.boxes, vol J (f (π.tag J))

theorem integralSum_biUnionTagged (f : ℝⁿ → E) (vol : ι →ᵇᵃ E →L[ℝ] F) (π : Prepartition I)
    (πi : ∀ J, TaggedPrepartition J) :
    integralSum f vol (π.biUnionTagged πi) = ∑ J ∈ π.boxes, integralSum f vol (πi J) := by
  refine (π.sum_biUnion_boxes _ _).trans <| sum_congr rfl fun J hJ => sum_congr rfl fun J' hJ' => ?_
  rw [π.tag_biUnionTagged hJ hJ']

theorem integralSum_biUnion_partition (f : ℝⁿ → E) (vol : ι →ᵇᵃ E →L[ℝ] F)
    (π : TaggedPrepartition I) (πi : ∀ J, Prepartition J) (hπi : ∀ J ∈ π, (πi J).IsPartition) :
    integralSum f vol (π.biUnionPrepartition πi) = integralSum f vol π := by
  refine (π.sum_biUnion_boxes _ _).trans (sum_congr rfl fun J hJ => ?_)
  calc
    (∑ J' ∈ (πi J).boxes, vol J' (f (π.tag <| π.toPrepartition.biUnionIndex πi J'))) =
        ∑ J' ∈ (πi J).boxes, vol J' (f (π.tag J)) :=
      sum_congr rfl fun J' hJ' => by rw [Prepartition.biUnionIndex_of_mem _ hJ hJ']
    _ = vol J (f (π.tag J)) :=
      (vol.map ⟨⟨fun g : E →L[ℝ] F => g (f (π.tag J)), rfl⟩, fun _ _ => rfl⟩).sum_partition_boxes
        le_top (hπi J hJ)

theorem integralSum_inf_partition (f : ℝⁿ → E) (vol : ι →ᵇᵃ E →L[ℝ] F) (π : TaggedPrepartition I)
    {π' : Prepartition I} (h : π'.IsPartition) :
    integralSum f vol (π.infPrepartition π') = integralSum f vol π :=
  integralSum_biUnion_partition f vol π _ fun _J hJ => h.restrict (Prepartition.le_of_mem _ hJ)

open Classical in

theorem integralSum_fiberwise {α} (g : Box ι → α) (f : ℝⁿ → E) (vol : ι →ᵇᵃ E →L[ℝ] F)
    (π : TaggedPrepartition I) :
    (∑ y ∈ π.boxes.image g, integralSum f vol (π.filter (g · = y))) = integralSum f vol π :=
  π.sum_fiberwise g fun J => vol J (f <| π.tag J)

theorem integralSum_sub_partitions (f : ℝⁿ → E) (vol : ι →ᵇᵃ E →L[ℝ] F)
    {π₁ π₂ : TaggedPrepartition I} (h₁ : π₁.IsPartition) (h₂ : π₂.IsPartition) :
    integralSum f vol π₁ - integralSum f vol π₂ =
      ∑ J ∈ (π₁.toPrepartition ⊓ π₂.toPrepartition).boxes,
        (vol J (f <| (π₁.infPrepartition π₂.toPrepartition).tag J) -
          vol J (f <| (π₂.infPrepartition π₁.toPrepartition).tag J)) := by
  rw [← integralSum_inf_partition f vol π₁ h₂, ← integralSum_inf_partition f vol π₂ h₁,
    integralSum, integralSum, Finset.sum_sub_distrib]
  simp only [infPrepartition_toPrepartition, inf_comm]
