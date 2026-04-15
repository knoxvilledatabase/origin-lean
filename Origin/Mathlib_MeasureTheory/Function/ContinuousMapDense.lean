/-
Extracted from MeasureTheory/Function/ContinuousMapDense.lean
Genuine: 8 of 13 | Dissolved: 5 | Infrastructure: 0
-/
import Origin.Core

/-!
# Approximation in Lᵖ by continuous functions

This file proves that bounded continuous functions are dense in `Lp E p μ`, for `p < ∞`, if the
domain `α` of the functions is a normal topological space and the measure `μ` is weakly regular.
It also proves the same results for approximation by continuous functions with compact support
when the space is locally compact and `μ` is regular.

The result is presented in several versions. First concrete versions giving an approximation
up to `ε` in these various contexts, and then abstract versions stating that the topological
closure of the relevant subgroups of `Lp` are the whole space.

* `MeasureTheory.MemLp.exists_hasCompactSupport_eLpNorm_sub_le` states that, in a locally compact
  space, an `ℒp` function can be approximated by continuous functions with compact support,
  in the sense that `eLpNorm (f - g) p μ` is small.
* `MeasureTheory.MemLp.exists_hasCompactSupport_integral_rpow_sub_le`: same result, but expressed in
  terms of `∫ ‖f - g‖^p`.

Versions with `Integrable` instead of `MemLp` are specialized to the case `p = 1`.
Versions with `boundedContinuous` instead of `HasCompactSupport` drop the locally
compact assumption and give only approximation by a bounded continuous function.

* `MeasureTheory.Lp.boundedContinuousFunction_dense`: The subgroup
  `MeasureTheory.Lp.boundedContinuousFunction` of `Lp E p μ`, the additive subgroup of
  `Lp E p μ` consisting of equivalence classes containing a continuous representative, is dense in
  `Lp E p μ`.
* `BoundedContinuousFunction.toLp_denseRange`: For finite-measure `μ`, the continuous linear
  map `BoundedContinuousFunction.toLp p μ 𝕜` from `α →ᵇ E` to `Lp E p μ` has dense range.
* `ContinuousMap.toLp_denseRange`: For compact `α` and finite-measure `μ`, the continuous linear
  map `ContinuousMap.toLp p μ 𝕜` from `C(α, E)` to `Lp E p μ` has dense range.

Note that for `p = ∞` this result is not true:  the characteristic function of the set `[0, ∞)` in
`ℝ` cannot be continuously approximated in `L∞`.

The proof is in three steps.  First, since simple functions are dense in `Lp`, it suffices to prove
the result for a scalar multiple of a characteristic function of a measurable set `s`. Secondly,
since the measure `μ` is weakly regular, the set `s` can be approximated above by an open set and
below by a closed set.  Finally, since the domain `α` is normal, we use Urysohn's lemma to find a
continuous function interpolating between these two sets.

## Related results

Are you looking for a result on "directional" approximation (above or below with respect to an
order) of functions whose codomain is `ℝ≥0∞` or `ℝ`, by semicontinuous functions?
See the Vitali-Carathéodory theorem,
in the file `Mathlib/MeasureTheory/Integral/Bochner/VitaliCaratheodory.lean`.
-/

open scoped ENNReal NNReal Topology BoundedContinuousFunction

open MeasureTheory TopologicalSpace ContinuousMap Set Bornology

variable {α : Type*} [TopologicalSpace α] [NormalSpace α]
  [MeasurableSpace α] [BorelSpace α]

variable {E : Type*} [NormedAddCommGroup E] {μ : Measure α} {p : ℝ≥0∞}

namespace MeasureTheory

variable [NormedSpace ℝ E]

-- DISSOLVED: exists_continuous_eLpNorm_sub_le_of_closed

-- DISSOLVED: MemLp.exists_hasCompactSupport_eLpNorm_sub_le

theorem MemLp.exists_hasCompactSupport_integral_rpow_sub_le
    [R1Space α] [WeaklyLocallyCompactSpace α] [μ.Regular]
    {p : ℝ} (hp : 0 < p) {f : α → E} (hf : MemLp f (ENNReal.ofReal p) μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : α → E,
      HasCompactSupport g ∧
        (∫ x, ‖f x - g x‖ ^ p ∂μ) ≤ ε ∧ Continuous g ∧ MemLp g (ENNReal.ofReal p) μ := by
  have I : 0 < ε ^ (1 / p) := Real.rpow_pos_of_pos hε _
  have A : ENNReal.ofReal (ε ^ (1 / p)) ≠ 0 := by
    simp only [Ne, ENNReal.ofReal_eq_zero, not_le, I]
  have B : ENNReal.ofReal p ≠ 0 := by simpa only [Ne, ENNReal.ofReal_eq_zero, not_le] using hp
  rcases hf.exists_hasCompactSupport_eLpNorm_sub_le ENNReal.coe_ne_top A with
    ⟨g, g_support, hg, g_cont, g_mem⟩
  change eLpNorm _ (ENNReal.ofReal p) _ ≤ _ at hg
  refine ⟨g, g_support, ?_, g_cont, g_mem⟩
  rwa [(hf.sub g_mem).eLpNorm_eq_integral_rpow_norm B ENNReal.coe_ne_top,
    ENNReal.ofReal_le_ofReal_iff I.le, one_div, ENNReal.toReal_ofReal hp.le,
    Real.rpow_le_rpow_iff _ hε.le (inv_pos.2 hp)] at hg
  positivity

-- DISSOLVED: Integrable.exists_hasCompactSupport_lintegral_sub_le

theorem Integrable.exists_hasCompactSupport_integral_sub_le
    [R1Space α] [WeaklyLocallyCompactSpace α] [μ.Regular]
    {f : α → E} (hf : Integrable f μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : α → E, HasCompactSupport g ∧ (∫ x, ‖f x - g x‖ ∂μ) ≤ ε ∧
      Continuous g ∧ Integrable g μ := by
  simp only [← memLp_one_iff_integrable, ← ENNReal.ofReal_one]
    at hf ⊢
  simpa using hf.exists_hasCompactSupport_integral_rpow_sub_le zero_lt_one hε

-- DISSOLVED: MemLp.exists_boundedContinuous_eLpNorm_sub_le

theorem MemLp.exists_boundedContinuous_integral_rpow_sub_le [μ.WeaklyRegular] {p : ℝ} (hp : 0 < p)
    {f : α → E} (hf : MemLp f (ENNReal.ofReal p) μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : α →ᵇ E, (∫ x, ‖f x - g x‖ ^ p ∂μ) ≤ ε ∧ MemLp g (ENNReal.ofReal p) μ := by
  have I : 0 < ε ^ (1 / p) := Real.rpow_pos_of_pos hε _
  have A : ENNReal.ofReal (ε ^ (1 / p)) ≠ 0 := by
    simp only [Ne, ENNReal.ofReal_eq_zero, not_le, I]
  have B : ENNReal.ofReal p ≠ 0 := by simpa only [Ne, ENNReal.ofReal_eq_zero, not_le] using hp
  rcases hf.exists_boundedContinuous_eLpNorm_sub_le ENNReal.coe_ne_top A with ⟨g, hg, g_mem⟩
  change eLpNorm _ (ENNReal.ofReal p) _ ≤ _ at hg
  refine ⟨g, ?_, g_mem⟩
  rwa [(hf.sub g_mem).eLpNorm_eq_integral_rpow_norm B ENNReal.coe_ne_top,
    ENNReal.ofReal_le_ofReal_iff I.le, one_div, ENNReal.toReal_ofReal hp.le,
    Real.rpow_le_rpow_iff _ hε.le (inv_pos.2 hp)] at hg
  positivity

-- DISSOLVED: Integrable.exists_boundedContinuous_lintegral_sub_le

theorem Integrable.exists_boundedContinuous_integral_sub_le [μ.WeaklyRegular] {f : α → E}
    (hf : Integrable f μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : α →ᵇ E, (∫ x, ‖f x - g x‖ ∂μ) ≤ ε ∧ Integrable g μ := by
  simp only [← memLp_one_iff_integrable, ← ENNReal.ofReal_one]
    at hf ⊢
  simpa using hf.exists_boundedContinuous_integral_rpow_sub_le zero_lt_one hε

namespace Lp

variable (E μ)

theorem boundedContinuousFunction_dense [SecondCountableTopologyEither α E] [Fact (1 ≤ p)]
    (hp : p ≠ ∞) [μ.WeaklyRegular] :
    Dense (boundedContinuousFunction E p μ : Set (Lp E p μ)) := by
  intro f
  refine (mem_closure_iff_nhds_basis Metric.nhds_basis_closedEBall).2 fun ε hε ↦ ?_
  obtain ⟨g, hg, g_mem⟩ :
      ∃ g : α →ᵇ E, eLpNorm ((f : α → E) - (g : α → E)) p μ ≤ ε ∧ MemLp g p μ :=
    (Lp.memLp f).exists_boundedContinuous_eLpNorm_sub_le hp hε.ne'
  refine ⟨g_mem.toLp _, ⟨g, rfl⟩, ?_⟩
  rwa [Metric.mem_closedEBall', ← Lp.toLp_coeFn f (Lp.memLp f), Lp.edist_toLp_toLp]

theorem boundedContinuousFunction_topologicalClosure [SecondCountableTopologyEither α E]
    [Fact (1 ≤ p)] (hp : p ≠ ∞) [μ.WeaklyRegular] :
    (boundedContinuousFunction E p μ).topologicalClosure = ⊤ :=
  SetLike.ext' <| (boundedContinuousFunction_dense E μ hp).closure_eq

end Lp

end MeasureTheory

variable [SecondCountableTopologyEither α E] [_i : Fact (1 ≤ p)]

variable (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] [NormedSpace ℝ E]

variable (E) (μ)

namespace BoundedContinuousFunction

theorem toLp_denseRange [μ.WeaklyRegular] [IsFiniteMeasure μ] (hp : p ≠ ∞) :
    DenseRange (toLp p μ 𝕜 : (α →ᵇ E) →L[𝕜] Lp E p μ) := by
  simpa only [← range_toLp p μ (𝕜 := 𝕜)]
    using MeasureTheory.Lp.boundedContinuousFunction_dense E μ hp

end BoundedContinuousFunction

namespace ContinuousMap

theorem toLp_denseRange [CompactSpace α] [μ.WeaklyRegular] [IsFiniteMeasure μ] (hp : p ≠ ∞) :
    DenseRange (toLp p μ 𝕜 : C(α, E) →L[𝕜] Lp E p μ) := by
  refine (BoundedContinuousFunction.toLp_denseRange _ _ 𝕜 hp).mono ?_
  refine range_subset_iff.2 fun f ↦ ?_
  exact ⟨f.toContinuousMap, rfl⟩

end ContinuousMap
