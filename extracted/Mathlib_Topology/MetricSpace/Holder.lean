/-
Extracted from Topology/MetricSpace/Holder.lean
Genuine: 39 | Conflates: 0 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

noncomputable section

/-!
# Hölder continuous functions

In this file we define Hölder continuity on a set and on the whole space. We also prove some basic
properties of Hölder continuous functions.

## Main definitions

* `HolderOnWith`: `f : X → Y` is said to be *Hölder continuous* with constant `C : ℝ≥0` and
  exponent `r : ℝ≥0` on a set `s`, if `edist (f x) (f y) ≤ C * edist x y ^ r` for all `x y ∈ s`;
* `HolderWith`: `f : X → Y` is said to be *Hölder continuous* with constant `C : ℝ≥0` and exponent
  `r : ℝ≥0`, if `edist (f x) (f y) ≤ C * edist x y ^ r` for all `x y : X`.

## Implementation notes

We use the type `ℝ≥0` (a.k.a. `NNReal`) for `C` because this type has coercion both to `ℝ` and
`ℝ≥0∞`, so it can be easily used both in inequalities about `dist` and `edist`. We also use `ℝ≥0`
for `r` to ensure that `d ^ r` is monotone in `d`. It might be a good idea to use
`ℝ>0` for `r` but we don't have this type in `mathlib` (yet).

## Tags

Hölder continuity, Lipschitz continuity

 -/

variable {X Y Z : Type*}

open Filter Set

open NNReal ENNReal Topology

section Emetric

variable [PseudoEMetricSpace X] [PseudoEMetricSpace Y] [PseudoEMetricSpace Z]

def HolderWith (C r : ℝ≥0) (f : X → Y) : Prop :=
  ∀ x y, edist (f x) (f y) ≤ (C : ℝ≥0∞) * edist x y ^ (r : ℝ)

def HolderOnWith (C r : ℝ≥0) (f : X → Y) (s : Set X) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, edist (f x) (f y) ≤ (C : ℝ≥0∞) * edist x y ^ (r : ℝ)

@[simp]
theorem holderOnWith_empty (C r : ℝ≥0) (f : X → Y) : HolderOnWith C r f ∅ := fun _ hx => hx.elim

@[simp]
theorem holderOnWith_singleton (C r : ℝ≥0) (f : X → Y) (x : X) : HolderOnWith C r f {x} := by
  rintro a (rfl : a = x) b (rfl : b = a)
  rw [edist_self]
  exact zero_le _

theorem Set.Subsingleton.holderOnWith {s : Set X} (hs : s.Subsingleton) (C r : ℝ≥0) (f : X → Y) :
    HolderOnWith C r f s :=
  hs.induction_on (holderOnWith_empty C r f) (holderOnWith_singleton C r f)

theorem holderOnWith_univ {C r : ℝ≥0} {f : X → Y} : HolderOnWith C r f univ ↔ HolderWith C r f := by
  simp only [HolderOnWith, HolderWith, mem_univ, true_imp_iff]

@[simp]
theorem holderOnWith_one {C : ℝ≥0} {f : X → Y} {s : Set X} :
    HolderOnWith C 1 f s ↔ LipschitzOnWith C f s := by
  simp only [HolderOnWith, LipschitzOnWith, NNReal.coe_one, ENNReal.rpow_one]

alias ⟨_, LipschitzOnWith.holderOnWith⟩ := holderOnWith_one

@[simp]
theorem holderWith_one {C : ℝ≥0} {f : X → Y} : HolderWith C 1 f ↔ LipschitzWith C f :=
  holderOnWith_univ.symm.trans <| holderOnWith_one.trans lipschitzOnWith_univ

alias ⟨_, LipschitzWith.holderWith⟩ := holderWith_one

theorem holderWith_id : HolderWith 1 1 (id : X → X) :=
  LipschitzWith.id.holderWith

protected theorem HolderWith.holderOnWith {C r : ℝ≥0} {f : X → Y} (h : HolderWith C r f)
    (s : Set X) : HolderOnWith C r f s := fun x _ y _ => h x y

namespace HolderOnWith

variable {C r : ℝ≥0} {f : X → Y} {s t : Set X}

theorem edist_le (h : HolderOnWith C r f s) {x y : X} (hx : x ∈ s) (hy : y ∈ s) :
    edist (f x) (f y) ≤ (C : ℝ≥0∞) * edist x y ^ (r : ℝ) :=
  h x hx y hy

theorem edist_le_of_le (h : HolderOnWith C r f s) {x y : X} (hx : x ∈ s) (hy : y ∈ s) {d : ℝ≥0∞}
    (hd : edist x y ≤ d) : edist (f x) (f y) ≤ (C : ℝ≥0∞) * d ^ (r : ℝ) :=
  (h.edist_le hx hy).trans <| by gcongr

theorem comp {Cg rg : ℝ≥0} {g : Y → Z} {t : Set Y} (hg : HolderOnWith Cg rg g t) {Cf rf : ℝ≥0}
    {f : X → Y} (hf : HolderOnWith Cf rf f s) (hst : MapsTo f s t) :
    HolderOnWith (Cg * Cf ^ (rg : ℝ)) (rg * rf) (g ∘ f) s := by
  intro x hx y hy
  rw [ENNReal.coe_mul, mul_comm rg, NNReal.coe_mul, ENNReal.rpow_mul, mul_assoc,
    ENNReal.coe_rpow_of_nonneg _ rg.coe_nonneg, ← ENNReal.mul_rpow_of_nonneg _ _ rg.coe_nonneg]
  exact hg.edist_le_of_le (hst hx) (hst hy) (hf.edist_le hx hy)

theorem comp_holderWith {Cg rg : ℝ≥0} {g : Y → Z} {t : Set Y} (hg : HolderOnWith Cg rg g t)
    {Cf rf : ℝ≥0} {f : X → Y} (hf : HolderWith Cf rf f) (ht : ∀ x, f x ∈ t) :
    HolderWith (Cg * Cf ^ (rg : ℝ)) (rg * rf) (g ∘ f) :=
  holderOnWith_univ.mp <| hg.comp (hf.holderOnWith univ) fun x _ => ht x

protected theorem uniformContinuousOn (hf : HolderOnWith C r f s) (h0 : 0 < r) :
    UniformContinuousOn f s := by
  refine EMetric.uniformContinuousOn_iff.2 fun ε εpos => ?_
  have : Tendsto (fun d : ℝ≥0∞ => (C : ℝ≥0∞) * d ^ (r : ℝ)) (𝓝 0) (𝓝 0) :=
    ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos ENNReal.coe_ne_top h0
  rcases ENNReal.nhds_zero_basis.mem_iff.1 (this (gt_mem_nhds εpos)) with ⟨δ, δ0, H⟩
  exact ⟨δ, δ0, fun hx y hy h => (hf.edist_le hx hy).trans_lt (H h)⟩

protected theorem continuousOn (hf : HolderOnWith C r f s) (h0 : 0 < r) : ContinuousOn f s :=
  (hf.uniformContinuousOn h0).continuousOn

protected theorem mono (hf : HolderOnWith C r f s) (ht : t ⊆ s) : HolderOnWith C r f t :=
  fun _ hx _ hy => hf.edist_le (ht hx) (ht hy)

theorem ediam_image_le_of_le (hf : HolderOnWith C r f s) {d : ℝ≥0∞} (hd : EMetric.diam s ≤ d) :
    EMetric.diam (f '' s) ≤ (C : ℝ≥0∞) * d ^ (r : ℝ) :=
  EMetric.diam_image_le_iff.2 fun _ hx _ hy =>
    hf.edist_le_of_le hx hy <| (EMetric.edist_le_diam_of_mem hx hy).trans hd

theorem ediam_image_le (hf : HolderOnWith C r f s) :
    EMetric.diam (f '' s) ≤ (C : ℝ≥0∞) * EMetric.diam s ^ (r : ℝ) :=
  hf.ediam_image_le_of_le le_rfl

theorem ediam_image_le_of_subset (hf : HolderOnWith C r f s) (ht : t ⊆ s) :
    EMetric.diam (f '' t) ≤ (C : ℝ≥0∞) * EMetric.diam t ^ (r : ℝ) :=
  (hf.mono ht).ediam_image_le

theorem ediam_image_le_of_subset_of_le (hf : HolderOnWith C r f s) (ht : t ⊆ s) {d : ℝ≥0∞}
    (hd : EMetric.diam t ≤ d) : EMetric.diam (f '' t) ≤ (C : ℝ≥0∞) * d ^ (r : ℝ) :=
  (hf.mono ht).ediam_image_le_of_le hd

theorem ediam_image_inter_le_of_le (hf : HolderOnWith C r f s) {d : ℝ≥0∞}
    (hd : EMetric.diam t ≤ d) : EMetric.diam (f '' (t ∩ s)) ≤ (C : ℝ≥0∞) * d ^ (r : ℝ) :=
  hf.ediam_image_le_of_subset_of_le inter_subset_right <|
    (EMetric.diam_mono inter_subset_left).trans hd

theorem ediam_image_inter_le (hf : HolderOnWith C r f s) (t : Set X) :
    EMetric.diam (f '' (t ∩ s)) ≤ (C : ℝ≥0∞) * EMetric.diam t ^ (r : ℝ) :=
  hf.ediam_image_inter_le_of_le le_rfl

end HolderOnWith

namespace HolderWith

variable {C r : ℝ≥0} {f : X → Y}

theorem edist_le (h : HolderWith C r f) (x y : X) :
    edist (f x) (f y) ≤ (C : ℝ≥0∞) * edist x y ^ (r : ℝ) :=
  h x y

theorem edist_le_of_le (h : HolderWith C r f) {x y : X} {d : ℝ≥0∞} (hd : edist x y ≤ d) :
    edist (f x) (f y) ≤ (C : ℝ≥0∞) * d ^ (r : ℝ) :=
  (h.holderOnWith univ).edist_le_of_le trivial trivial hd

theorem comp {Cg rg : ℝ≥0} {g : Y → Z} (hg : HolderWith Cg rg g) {Cf rf : ℝ≥0} {f : X → Y}
    (hf : HolderWith Cf rf f) : HolderWith (Cg * Cf ^ (rg : ℝ)) (rg * rf) (g ∘ f) :=
  (hg.holderOnWith univ).comp_holderWith hf fun _ => trivial

theorem comp_holderOnWith {Cg rg : ℝ≥0} {g : Y → Z} (hg : HolderWith Cg rg g) {Cf rf : ℝ≥0}
    {f : X → Y} {s : Set X} (hf : HolderOnWith Cf rf f s) :
    HolderOnWith (Cg * Cf ^ (rg : ℝ)) (rg * rf) (g ∘ f) s :=
  (hg.holderOnWith univ).comp hf fun _ _ => trivial

protected theorem uniformContinuous (hf : HolderWith C r f) (h0 : 0 < r) : UniformContinuous f :=
  uniformContinuousOn_univ.mp <| (hf.holderOnWith univ).uniformContinuousOn h0

protected theorem continuous (hf : HolderWith C r f) (h0 : 0 < r) : Continuous f :=
  (hf.uniformContinuous h0).continuous

theorem ediam_image_le (hf : HolderWith C r f) (s : Set X) :
    EMetric.diam (f '' s) ≤ (C : ℝ≥0∞) * EMetric.diam s ^ (r : ℝ) :=
  EMetric.diam_image_le_iff.2 fun _ hx _ hy =>
    hf.edist_le_of_le <| EMetric.edist_le_diam_of_mem hx hy

lemma const {y : Y} :
    HolderWith C r (Function.const X y) := fun x₁ x₂ => by
  simp only [Function.const_apply, edist_self, zero_le]

lemma zero [Zero Y] : HolderWith C r (0 : X → Y) := .const

lemma of_isEmpty [IsEmpty X] : HolderWith C r f := isEmptyElim

lemma mono {C' : ℝ≥0} (hf : HolderWith C r f) (h : C ≤ C') :
    HolderWith C' r f :=
  fun x₁ x₂ ↦ (hf x₁ x₂).trans (mul_right_mono (coe_le_coe.2 h))

end HolderWith

end Emetric

section PseudoMetric

variable [PseudoMetricSpace X] [PseudoMetricSpace Y] {C r : ℝ≥0} {f : X → Y}

namespace HolderWith

theorem nndist_le_of_le (hf : HolderWith C r f) {x y : X} {d : ℝ≥0} (hd : nndist x y ≤ d) :
    nndist (f x) (f y) ≤ C * d ^ (r : ℝ) := by
  rw [← ENNReal.coe_le_coe, ← edist_nndist, ENNReal.coe_mul,
    ENNReal.coe_rpow_of_nonneg _ r.coe_nonneg]
  apply hf.edist_le_of_le
  rwa [edist_nndist, ENNReal.coe_le_coe]

theorem nndist_le (hf : HolderWith C r f) (x y : X) :
    nndist (f x) (f y) ≤ C * nndist x y ^ (r : ℝ) :=
  hf.nndist_le_of_le le_rfl

theorem dist_le_of_le (hf : HolderWith C r f) {x y : X} {d : ℝ} (hd : dist x y ≤ d) :
    dist (f x) (f y) ≤ C * d ^ (r : ℝ) := by
  lift d to ℝ≥0 using dist_nonneg.trans hd
  rw [dist_nndist] at hd ⊢
  norm_cast at hd ⊢
  exact hf.nndist_le_of_le hd

theorem dist_le (hf : HolderWith C r f) (x y : X) : dist (f x) (f y) ≤ C * dist x y ^ (r : ℝ) :=
  hf.dist_le_of_le le_rfl

end HolderWith

end PseudoMetric

section Metric

variable [PseudoMetricSpace X] [MetricSpace Y] {r : ℝ≥0} {f : X → Y}

@[simp]
lemma holderWith_zero_iff : HolderWith 0 r f ↔ ∀ x₁ x₂, f x₁ = f x₂ := by
  refine ⟨fun h x₁ x₂ => ?_, fun h x₁ x₂ => h x₁ x₂ ▸ ?_⟩
  · specialize h x₁ x₂
    simp [ENNReal.coe_zero, zero_mul, nonpos_iff_eq_zero, edist_eq_zero] at h
    assumption
  · simp only [edist_self, ENNReal.coe_zero, zero_mul, le_refl]

end Metric

section SeminormedAddCommGroup

variable [PseudoMetricSpace X] [SeminormedAddCommGroup Y] {C C' r : ℝ≥0} {f g : X → Y}

namespace HolderWith

lemma add (hf : HolderWith C r f) (hg : HolderWith C' r g) :
    HolderWith (C + C') r (f + g) := fun x₁ x₂ => by
  refine le_trans (edist_add_add_le _ _ _ _) <| le_trans (add_le_add (hf x₁ x₂) (hg x₁ x₂)) ?_
  rw [coe_add, add_mul]

lemma smul {α} [NormedDivisionRing α] [Module α Y] [BoundedSMul α Y] (a : α)
    (hf : HolderWith C r f) : HolderWith (C * ‖a‖₊) r (a • f) := fun x₁ x₂ => by
  rw [Pi.smul_apply, coe_mul, Pi.smul_apply, edist_smul₀, mul_comm (C : ℝ≥0∞),
    ENNReal.smul_def, smul_eq_mul, mul_assoc]
  gcongr
  exact hf x₁ x₂

end HolderWith

end SeminormedAddCommGroup
