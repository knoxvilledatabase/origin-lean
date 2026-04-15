/-
Extracted from Analysis/Convolution.lean
Genuine: 29 of 34 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-!
# Convolution of functions

This file defines the convolution on two functions, i.e. `x ↦ ∫ f(t)g(x - t) ∂t`.
In the general case, these functions can be vector-valued, and have an arbitrary (additive)
group as domain. We use a continuous bilinear operation `L` on these function values as
"multiplication". The domain must be equipped with a Haar measure `μ`
(though many individual results have weaker conditions on `μ`).

For many applications we can take `L = ContinuousLinearMap.lsmul ℝ ℝ` or
`L = ContinuousLinearMap.mul ℝ ℝ`.

We also define `ConvolutionExists` and `ConvolutionExistsAt` to state that the convolution is
well-defined (everywhere or at a single point). These conditions are needed for pointwise
computations (e.g. `ConvolutionExistsAt.distrib_add`), but are generally not strong enough for any
local (or global) properties of the convolution. For this we need stronger assumptions on `f`
and/or `g`, and generally if we impose stronger conditions on one of the functions, we can impose
weaker conditions on the other.
We have proven many of the properties of the convolution assuming one of these functions
has compact support (in which case the other function only needs to be locally integrable).
We still need to prove the properties for other pairs of conditions (e.g. both functions are
rapidly decreasing)

## Design Decisions

We use a bilinear map `L` to "multiply" the two functions in the integrand.
This generality has several advantages

* This allows us to compute the total derivative of the convolution, in case the functions are
  multivariate. The total derivative is again a convolution, but where the codomains of the
  functions can be higher-dimensional. See `HasCompactSupport.hasFDerivAt_convolution_right`.
* This allows us to use `@[to_additive]` everywhere (which would not be possible if we would use
  `mul`/`smul` in the integral, since `@[to_additive]` will incorrectly also try to additivize
  those definitions).
* We need to support the case where at least one of the functions is vector-valued, but if we use
  `smul` to multiply the functions, that would be an asymmetric definition.

## Main Definitions

* `MeasureTheory.convolution f g L μ x = (f ⋆[L, μ] g) x = ∫ t, L (f t) (g (x - t)) ∂μ`
  is the convolution of `f` and `g` w.r.t. the continuous bilinear map `L` and measure `μ`.
* `MeasureTheory.ConvolutionExistsAt f g x L μ` states that the convolution `(f ⋆[L, μ] g) x`
  is well-defined (i.e. the integral exists).
* `MeasureTheory.ConvolutionExists f g L μ` states that the convolution `f ⋆[L, μ] g`
  is well-defined at each point.

## Main Results

* `MeasureTheory.convolution_tendsto_right`: Given a sequence of nonnegative normalized functions
  whose support tends to a small neighborhood around `0`, the convolution tends to the right
  argument. This is specialized to bump functions in `ContDiffBump.convolution_tendsto_right`.

## Notation

The following notations are localized in the scope `Convolution`:
* `f ⋆[L, μ] g` for the convolution. Note: you have to use parentheses to apply the convolution
  to an argument: `(f ⋆[L, μ] g) x`.
* `f ⋆[L] g := f ⋆[L, volume] g`
* `f ⋆ g := f ⋆[lsmul ℝ ℝ] g`

## To do

* Existence and (uniform) continuity of the convolution if
  one of the maps is in `ℒ^p` and the other in `ℒ^q` with `1 / p + 1 / q = 1`.
  This might require a generalization of `MeasureTheory.MemLp.smul` where `smul` is generalized
  to a continuous bilinear map.
  (see e.g. [Fremlin, *Measure Theory* (volume 2)][fremlin_vol2], 255K)
* The convolution is an `AEStronglyMeasurable` function
  (see e.g. [Fremlin, *Measure Theory* (volume 2)][fremlin_vol2], 255I).
* Prove properties about the convolution if both functions are rapidly decreasing.
* Use `@[to_additive]` everywhere (this likely requires changes in `to_additive`)
-/

assert_not_exists ContDiffAt HasDerivAt

open Set Function Filter MeasureTheory MeasureTheory.Measure TopologicalSpace

open Bornology ContinuousLinearMap Metric Topology

open scoped Pointwise NNReal Filter

universe u𝕜 uG uE uE' uE'' uF uF' uF'' uP

variable {𝕜 : Type u𝕜} {G : Type uG} {E : Type uE} {E' : Type uE'} {E'' : Type uE''} {F : Type uF}
  {F' : Type uF'} {F'' : Type uF''} {P : Type uP}

variable [NormedAddCommGroup E] [NormedAddCommGroup E'] [NormedAddCommGroup E'']
  [NormedAddCommGroup F] {f f' : G → E} {g g' : G → E'} {x x' : G} {y y' : E}

namespace MeasureTheory

section NontriviallyNormedField

variable [NontriviallyNormedField 𝕜]

variable [NormedSpace 𝕜 E] [NormedSpace 𝕜 E'] [NormedSpace 𝕜 E''] [NormedSpace 𝕜 F]

variable (L : E →L[𝕜] E' →L[𝕜] F)

section NoMeasurability

variable [AddGroup G] [TopologicalSpace G]

theorem convolution_integrand_bound_right_of_le_of_subset {C : ℝ} (hC : ∀ i, ‖g i‖ ≤ C) {x t : G}
    {s u : Set G} (hx : x ∈ s) (hu : -tsupport g + s ⊆ u) :
    ‖L (f t) (g (x - t))‖ ≤ u.indicator (fun t => ‖L‖ * ‖f t‖ * C) t := by
  -- Porting note: had to add `f := _`
  refine le_indicator (f := fun t ↦ ‖L (f t) (g (x - t))‖) (fun t _ => ?_) (fun t ht => ?_) t
  · apply_rules [L.le_of_opNorm₂_le_of_le, le_rfl]
  · have : x - t ∉ support g := by
      refine mt (fun hxt => hu ?_) ht
      refine ⟨_, Set.neg_mem_neg.mpr (subset_closure hxt), _, hx, ?_⟩
      simp only [neg_sub, sub_add_cancel]
    simp only [notMem_support.mp this, (L _).map_zero, norm_zero, le_rfl]

theorem _root_.HasCompactSupport.convolution_integrand_bound_right_of_subset
    (hcg : HasCompactSupport g) (hg : Continuous g)
    {x t : G} {s u : Set G} (hx : x ∈ s) (hu : -tsupport g + s ⊆ u) :
    ‖L (f t) (g (x - t))‖ ≤ u.indicator (fun t => ‖L‖ * ‖f t‖ * ⨆ i, ‖g i‖) t := by
  refine convolution_integrand_bound_right_of_le_of_subset _ (fun i => ?_) hx hu
  exact le_ciSup (hg.norm.bddAbove_range_of_hasCompactSupport hcg.norm) _

theorem _root_.HasCompactSupport.convolution_integrand_bound_right (hcg : HasCompactSupport g)
    (hg : Continuous g) {x t : G} {s : Set G} (hx : x ∈ s) :
    ‖L (f t) (g (x - t))‖ ≤ (-tsupport g + s).indicator (fun t => ‖L‖ * ‖f t‖ * ⨆ i, ‖g i‖) t :=
  hcg.convolution_integrand_bound_right_of_subset L hg hx Subset.rfl

theorem _root_.Continuous.convolution_integrand_fst [ContinuousSub G] (hg : Continuous g) (t : G) :
    Continuous fun x => L (f t) (g (x - t)) :=
  L.continuous₂.comp₂ continuous_const <| by fun_prop

theorem _root_.HasCompactSupport.convolution_integrand_bound_left (hcf : HasCompactSupport f)
    (hf : Continuous f) {x t : G} {s : Set G} (hx : x ∈ s) :
    ‖L (f (x - t)) (g t)‖ ≤
      (-tsupport f + s).indicator (fun t => (‖L‖ * ⨆ i, ‖f i‖) * ‖g t‖) t := by
  convert hcf.convolution_integrand_bound_right L.flip hf hx using 1
  simp_rw [L.opNorm_flip, mul_right_comm]

end NoMeasurability

section Measurability

variable [MeasurableSpace G] {μ ν : Measure G}

def ConvolutionExistsAt [Sub G] (f : G → E) (g : G → E') (x : G) (L : E →L[𝕜] E' →L[𝕜] F)
    (μ : Measure G := by volume_tac) : Prop :=
  Integrable (fun t => L (f t) (g (x - t))) μ

def ConvolutionExists [Sub G] (f : G → E) (g : G → E') (L : E →L[𝕜] E' →L[𝕜] F)
    (μ : Measure G := by volume_tac) : Prop :=
  ∀ x : G, ConvolutionExistsAt f g x L μ

section ConvolutionExists

variable {L} in

section Group

variable [AddGroup G]

theorem AEStronglyMeasurable.convolution_integrand' [MeasurableAdd₂ G]
    [MeasurableNeg G] (hf : AEStronglyMeasurable f ν)
    (hg : AEStronglyMeasurable g <| map (fun p : G × G => p.1 - p.2) (μ.prod ν)) :
    AEStronglyMeasurable (fun p : G × G => L (f p.2) (g (p.1 - p.2))) (μ.prod ν) :=
  L.aestronglyMeasurable_comp₂ hf.comp_snd <| hg.comp_measurable measurable_sub

variable [MeasurableAdd G] [MeasurableNeg G]

theorem AEStronglyMeasurable.convolution_integrand_snd'
    (hf : AEStronglyMeasurable f μ) {x : G}
    (hg : AEStronglyMeasurable g <| map (fun t => x - t) μ) :
    AEStronglyMeasurable (fun t => L (f t) (g (x - t))) μ :=
  L.aestronglyMeasurable_comp₂ hf <| hg.comp_measurable <| measurable_id.const_sub x

theorem AEStronglyMeasurable.convolution_integrand_swap_snd' {x : G}
    (hf : AEStronglyMeasurable f <| map (fun t => x - t) μ) (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (fun t => L (f (x - t)) (g t)) μ :=
  L.aestronglyMeasurable_comp₂ (hf.comp_measurable <| measurable_id.const_sub x) hg

theorem _root_.BddAbove.convolutionExistsAt' {x₀ : G} {s : Set G}
    (hbg : BddAbove ((fun i => ‖g i‖) '' ((fun t => -t + x₀) ⁻¹' s))) (hs : MeasurableSet s)
    (h2s : (support fun t => L (f t) (g (x₀ - t))) ⊆ s) (hf : IntegrableOn f s μ)
    (hmg : AEStronglyMeasurable g <| map (fun t => x₀ - t) (μ.restrict s)) :
    ConvolutionExistsAt f g x₀ L μ := by
  rw [ConvolutionExistsAt]
  rw [← integrableOn_iff_integrable_of_support_subset h2s]
  set s' := (fun t => -t + x₀) ⁻¹' s
  have : ∀ᵐ t : G ∂μ.restrict s,
      ‖L (f t) (g (x₀ - t))‖ ≤ s.indicator (fun t => ‖L‖ * ‖f t‖ * ⨆ i : s', ‖g i‖) t := by
    filter_upwards
    refine le_indicator (fun t ht => ?_) fun t ht => ?_
    · apply_rules [L.le_of_opNorm₂_le_of_le, le_rfl]
      refine (le_ciSup_set hbg <| mem_preimage.mpr ?_)
      rwa [neg_sub, sub_add_cancel]
    · have : t ∉ support fun t => L (f t) (g (x₀ - t)) := mt (fun h => h2s h) ht
      rw [notMem_support.mp this, norm_zero]
  refine Integrable.mono' ?_ ?_ this
  · rw [integrable_indicator_iff hs]; exact ((hf.norm.const_mul _).mul_const _).integrableOn
  · exact hf.aestronglyMeasurable.convolution_integrand_snd' L hmg

theorem ConvolutionExistsAt.of_norm' {x₀ : G}
    (h : ConvolutionExistsAt (fun x => ‖f x‖) (fun x => ‖g x‖) x₀ (mul ℝ ℝ) μ)
    (hmf : AEStronglyMeasurable f μ) (hmg : AEStronglyMeasurable g <| map (fun t => x₀ - t) μ) :
    ConvolutionExistsAt f g x₀ L μ := by
  refine (h.const_mul ‖L‖).mono'
    (hmf.convolution_integrand_snd' L hmg) (Eventually.of_forall fun x => ?_)
  rw [mul_apply', ← mul_assoc]
  apply L.le_opNorm₂

end

section Left

variable [MeasurableAdd₂ G] [MeasurableNeg G] [SFinite μ] [IsAddRightInvariant μ]

theorem AEStronglyMeasurable.convolution_integrand_snd (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (x : G) :
    AEStronglyMeasurable (fun t => L (f t) (g (x - t))) μ :=
  hf.convolution_integrand_snd' L <|
    hg.mono_ac <| (quasiMeasurePreserving_sub_left_of_right_invariant μ x).absolutelyContinuous

theorem AEStronglyMeasurable.convolution_integrand_swap_snd
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) (x : G) :
    AEStronglyMeasurable (fun t => L (f (x - t)) (g t)) μ :=
  (hf.mono_ac
        (quasiMeasurePreserving_sub_left_of_right_invariant μ
            x).absolutelyContinuous).convolution_integrand_swap_snd'
    L hg

end Left

section Right

variable [MeasurableAdd₂ G] [MeasurableNeg G] [SFinite μ] [IsAddRightInvariant μ] [SFinite ν]

theorem AEStronglyMeasurable.convolution_integrand (hf : AEStronglyMeasurable f ν)
    (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (fun p : G × G => L (f p.2) (g (p.1 - p.2))) (μ.prod ν) :=
  hf.convolution_integrand' L <|
    hg.mono_ac (quasiMeasurePreserving_sub_of_right_invariant μ ν).absolutelyContinuous

theorem Integrable.convolution_integrand (hf : Integrable f ν) (hg : Integrable g μ) :
    Integrable (fun p : G × G => L (f p.2) (g (p.1 - p.2))) (μ.prod ν) := by
  have h_meas : AEStronglyMeasurable (fun p : G × G => L (f p.2) (g (p.1 - p.2))) (μ.prod ν) :=
    hf.aestronglyMeasurable.convolution_integrand L hg.aestronglyMeasurable
  have h2_meas : AEStronglyMeasurable (fun y : G => ∫ x : G, ‖L (f y) (g (x - y))‖ ∂μ) ν :=
    h_meas.prod_swap.norm.integral_prod_right'
  simp_rw [integrable_prod_iff' h_meas]
  refine ⟨Eventually.of_forall fun t => (L (f t)).integrable_comp (hg.comp_sub_right t), ?_⟩
  refine Integrable.mono' ?_ h2_meas
      (Eventually.of_forall fun t => (?_ : _ ≤ ‖L‖ * ‖f t‖ * ∫ x, ‖g (x - t)‖ ∂μ))
  · simp only [integral_sub_right_eq_self (‖g ·‖)]
    fun_prop
  · simp_rw [← integral_const_mul]
    rw [Real.norm_of_nonneg (by positivity)]
    exact integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg _)
      ((hg.comp_sub_right t).norm.const_mul _) (Eventually.of_forall fun t => L.le_opNorm₂ _ _)

theorem Integrable.ae_convolution_exists (hf : Integrable f ν) (hg : Integrable g μ) :
    ∀ᵐ x ∂μ, ConvolutionExistsAt f g x L ν :=
  ((integrable_prod_iff <|
          hf.aestronglyMeasurable.convolution_integrand L hg.aestronglyMeasurable).mp <|
      hf.convolution_integrand L hg).1

end Right

variable [TopologicalSpace G] [IsTopologicalAddGroup G] [BorelSpace G]

theorem _root_.HasCompactSupport.convolutionExistsAt {x₀ : G}
    (h : HasCompactSupport fun t => L (f t) (g (x₀ - t))) (hf : LocallyIntegrable f μ)
    (hg : Continuous g) : ConvolutionExistsAt f g x₀ L μ := by
  let u := (Homeomorph.neg G).trans (Homeomorph.addRight x₀)
  let v := (Homeomorph.neg G).trans (Homeomorph.addLeft x₀)
  apply ((u.isCompact_preimage.mpr h).bddAbove_image hg.norm.continuousOn).convolutionExistsAt' L
    isClosed_closure.measurableSet subset_closure (hf.integrableOn_isCompact h)
  have A : AEStronglyMeasurable (g ∘ v)
      (μ.restrict (tsupport fun t : G => L (f t) (g (x₀ - t)))) := by
    apply (hg.comp v.continuous).continuousOn.aestronglyMeasurable_of_isCompact h
    exact (isClosed_tsupport _).measurableSet
  convert ((v.continuous.measurable.measurePreserving
      (μ.restrict (tsupport fun t => L (f t) (g (x₀ - t))))).aestronglyMeasurable_comp_iff
    v.measurableEmbedding).1 A
  ext x
  simp only [v, Homeomorph.neg, sub_eq_add_neg, val_toAddUnits_apply, Homeomorph.trans_apply,
    Equiv.neg_apply, Homeomorph.homeomorph_mk_coe, Homeomorph.coe_addLeft]

theorem _root_.HasCompactSupport.convolutionExists_right (hcg : HasCompactSupport g)
    (hf : LocallyIntegrable f μ) (hg : Continuous g) : ConvolutionExists f g L μ := by
  intro x₀
  refine HasCompactSupport.convolutionExistsAt L ?_ hf hg
  refine (hcg.comp_homeomorph (Homeomorph.subLeft x₀)).mono ?_
  refine fun t => mt fun ht : g (x₀ - t) = 0 => ?_
  simp_rw [ht, (L _).map_zero]

theorem _root_.HasCompactSupport.convolutionExists_left_of_continuous_right
    (hcf : HasCompactSupport f) (hf : LocallyIntegrable f μ) (hg : Continuous g) :
    ConvolutionExists f g L μ := by
  intro x₀
  refine HasCompactSupport.convolutionExistsAt L ?_ hf hg
  refine hcf.mono ?_
  refine fun t => mt fun ht : f t = 0 => ?_
  simp_rw [ht, L.map_zero₂]

end Group

section CommGroup

variable [AddCommGroup G]

section MeasurableGroup

variable [MeasurableNeg G] [IsAddLeftInvariant μ]

theorem _root_.BddAbove.convolutionExistsAt [MeasurableAdd₂ G] [SFinite μ] {x₀ : G} {s : Set G}
    (hbg : BddAbove ((fun i => ‖g i‖) '' ((fun t => x₀ - t) ⁻¹' s))) (hs : MeasurableSet s)
    (h2s : (support fun t => L (f t) (g (x₀ - t))) ⊆ s) (hf : IntegrableOn f s μ)
    (hmg : AEStronglyMeasurable g μ) : ConvolutionExistsAt f g x₀ L μ := by
  refine BddAbove.convolutionExistsAt' L ?_ hs h2s hf ?_
  · simp_rw [← sub_eq_neg_add, hbg]
  · have : AEStronglyMeasurable g (map (fun t : G => x₀ - t) μ) :=
      hmg.mono_ac (quasiMeasurePreserving_sub_left_of_right_invariant μ x₀).absolutelyContinuous
    apply this.mono_measure
    exact map_mono restrict_le_self (measurable_const.sub measurable_id')

variable {L} [MeasurableAdd G] [IsNegInvariant μ]

theorem convolutionExistsAt_flip :
    ConvolutionExistsAt g f x L.flip μ ↔ ConvolutionExistsAt f g x L μ := by
  simp_rw [ConvolutionExistsAt, ← integrable_comp_sub_left (fun t => L (f t) (g (x - t))) x,
    sub_sub_cancel, flip_apply]

theorem ConvolutionExistsAt.integrable_swap (h : ConvolutionExistsAt f g x L μ) :
    Integrable (fun t => L (f (x - t)) (g t)) μ := by
  convert h.comp_sub_left x
  simp_rw [sub_sub_self]

theorem convolutionExistsAt_iff_integrable_swap :
    ConvolutionExistsAt f g x L μ ↔ Integrable (fun t => L (f (x - t)) (g t)) μ :=
  convolutionExistsAt_flip.symm

end MeasurableGroup

variable [TopologicalSpace G] [IsTopologicalAddGroup G] [BorelSpace G]

variable [IsAddLeftInvariant μ] [IsNegInvariant μ]

theorem _root_.HasCompactSupport.convolutionExists_left
    (hcf : HasCompactSupport f) (hf : Continuous f)
    (hg : LocallyIntegrable g μ) : ConvolutionExists f g L μ := fun x₀ =>
  convolutionExistsAt_flip.mp <| hcf.convolutionExists_right L.flip hg hf x₀

theorem _root_.HasCompactSupport.convolutionExists_right_of_continuous_left
    (hcg : HasCompactSupport g) (hf : Continuous f) (hg : LocallyIntegrable g μ) :
    ConvolutionExists f g L μ := fun x₀ =>
  convolutionExistsAt_flip.mp <| hcg.convolutionExists_left_of_continuous_right L.flip hg hf x₀

end CommGroup

end ConvolutionExists

variable [NormedSpace ℝ F]

noncomputable def convolution [Sub G] (f : G → E) (g : G → E') (L : E →L[𝕜] E' →L[𝕜] F)
    (μ : Measure G := by volume_tac) : G → F := fun x =>
  ∫ t, L (f t) (g (x - t)) ∂μ

scoped[Convolution] notation:67 f " ⋆[" L:67 ", " μ:67 "] " g:66 => convolution f g L μ

scoped[Convolution]

  notation:67 f " ⋆[" L:67 "] " g:66 => convolution f g L MeasureSpace.volume

scoped[Convolution]

  notation:67 f " ⋆ " g:66 =>

    convolution f g (ContinuousLinearMap.lsmul ℝ ℝ) MeasureSpace.volume

open scoped Convolution

section Group

variable {L} [AddGroup G]

theorem smul_convolution [SMulCommClass ℝ 𝕜 F] {y : 𝕜} : y • f ⋆[L, μ] g = y • (f ⋆[L, μ] g) := by
  ext; simp only [Pi.smul_apply, convolution_def, ← integral_smul, L.map_smul₂]

theorem convolution_smul [SMulCommClass ℝ 𝕜 F] {y : 𝕜} : f ⋆[L, μ] y • g = y • (f ⋆[L, μ] g) := by
  ext; simp only [Pi.smul_apply, convolution_def, ← integral_smul, (L _).map_smul]
