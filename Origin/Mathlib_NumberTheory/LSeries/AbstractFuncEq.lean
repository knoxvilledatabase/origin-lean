/-
Extracted from NumberTheory/LSeries/AbstractFuncEq.lean
Genuine: 29 of 33 | Dissolved: 2 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.Analysis.MellinTransform

/-!
# Abstract functional equations for Mellin transforms

This file formalises a general version of an argument used to prove functional equations for
zeta and L functions.

### FE-pairs

We define a *weak FE-pair* to be a pair of functions `f, g` on the reals which are locally
integrable on `(0, ∞)`, have the form "constant" + "rapidly decaying term" at `∞`, and satisfy a
functional equation of the form

`f (1 / x) = ε * x ^ k * g x`

for some constants `k ∈ ℝ` and `ε ∈ ℂ`. (Modular forms give rise to natural examples
with `k` being the weight and `ε` the global root number; hence the notation.) We could arrange
`ε = 1` by scaling `g`; but this is inconvenient in applications so we set things up more generally.

A *strong FE-pair* is a weak FE-pair where the constant terms of `f` and `g` at `∞` are both 0.

The main property of these pairs is the following: if `f`, `g` are a weak FE-pair, with constant
terms `f₀` and `g₀` at `∞`, then the Mellin transforms `Λ` and `Λ'` of `f - f₀` and `g - g₀`
respectively both have meromorphic continuation and satisfy a functional equation of the form

`Λ (k - s) = ε * Λ' s`.

The poles (and their residues) are explicitly given in terms of `f₀` and `g₀`; in particular, if
`(f, g)` are a strong FE-pair, then the Mellin transforms of `f` and `g` are entire functions.

### Main definitions and results

See the sections *Main theorems on weak FE-pairs* and
*Main theorems on strong FE-pairs* below.

* Strong FE pairs:
  - `StrongFEPair.Λ` : function of `s : ℂ`
  - `StrongFEPair.differentiable_Λ`: `Λ` is entire
  - `StrongFEPair.hasMellin`: `Λ` is everywhere equal to the Mellin transform of `f`
  - `StrongFEPair.functional_equation`: the functional equation for `Λ`
* Weak FE pairs:
  - `WeakFEPair.Λ₀`: and `WeakFEPair.Λ`: functions of `s : ℂ`
  - `WeakFEPair.differentiable_Λ₀`: `Λ₀` is entire
  - `WeakFEPair.differentiableAt_Λ`: `Λ` is differentiable away from `s = 0` and `s = k`
  - `WeakFEPair.hasMellin`: for `k < re s`, `Λ s` equals the Mellin transform of `f - f₀`
  - `WeakFEPair.functional_equation₀`: the functional equation for `Λ₀`
  - `WeakFEPair.functional_equation`: the functional equation for `Λ`
  - `WeakFEPair.Λ_residue_k`: computation of the residue at `k`
  - `WeakFEPair.Λ_residue_zero`: computation of the residue at `0`.
-/

noncomputable section

open Real Complex Filter Topology Asymptotics Set MeasureTheory

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]

/-!
## Definitions and symmetry
-/

-- DISSOLVED: WeakFEPair

structure StrongFEPair extends WeakFEPair E where (hf₀ : f₀ = 0) (hg₀ : g₀ = 0)

variable {E}

section symmetry

lemma WeakFEPair.h_feq' (P : WeakFEPair E) (x : ℝ) (hx : 0 < x) :
    P.g (1 / x) = (P.ε⁻¹ * ↑(x ^ P.k)) • P.f x := by
  rw [(div_div_cancel₀ (one_ne_zero' ℝ) ▸ P.h_feq (1 / x) (one_div_pos.mpr hx):), ← mul_smul]
  convert (one_smul ℂ (P.g (1 / x))).symm using 2
  rw [one_div, inv_rpow hx.le, ofReal_inv]
  field_simp [P.hε, (rpow_pos_of_pos hx _).ne']

def WeakFEPair.symm (P : WeakFEPair E) : WeakFEPair E where
  hf_int := P.hg_int
  hg_int := P.hf_int
  hf_top := P.hg_top
  hg_top := P.hf_top
  hε     := inv_ne_zero P.hε
  hk     := P.hk
  h_feq  := P.h_feq'

def StrongFEPair.symm (P : StrongFEPair E) : StrongFEPair E where
  toWeakFEPair := P.toWeakFEPair.symm
  hf₀ := P.hg₀
  hg₀ := P.hf₀

end symmetry

namespace WeakFEPair

/-!
## Auxiliary results I: lemmas on asymptotics
-/

lemma hf_zero (P : WeakFEPair E) (r : ℝ) :
    (fun x ↦ P.f x - (P.ε * ↑(x ^ (-P.k))) • P.g₀) =O[𝓝[>] 0] (· ^ r) := by
  have := (P.hg_top (-(r + P.k))).comp_tendsto tendsto_inv_zero_atTop
  simp_rw [IsBigO, IsBigOWith, eventually_nhdsWithin_iff] at this ⊢
  obtain ⟨C, hC⟩ := this
  use ‖P.ε‖ * C
  filter_upwards [hC] with x hC' (hx : 0 < x)
  have h_nv2 : ↑(x ^ P.k) ≠ (0 : ℂ) := ofReal_ne_zero.mpr (rpow_pos_of_pos hx _).ne'
  have h_nv : P.ε⁻¹ * ↑(x ^ P.k) ≠ 0 := mul_ne_zero P.symm.hε h_nv2
  specialize hC' hx
  simp_rw [Function.comp_apply, ← one_div, P.h_feq' _ hx] at hC'
  rw [← ((mul_inv_cancel₀ h_nv).symm ▸ one_smul ℂ P.g₀ :), mul_smul _ _ P.g₀, ← smul_sub, norm_smul,
    ← le_div_iff₀' (lt_of_le_of_ne (norm_nonneg _) (norm_ne_zero_iff.mpr h_nv).symm)] at hC'
  convert hC' using 1
  · congr 3
    rw [rpow_neg hx.le]
    field_simp
  · simp_rw [norm_mul, norm_real, one_div, inv_rpow hx.le, rpow_neg hx.le, inv_inv, norm_inv,
      norm_of_nonneg (rpow_pos_of_pos hx _).le, rpow_add hx]
    field_simp
    ring

lemma hf_zero' (P : WeakFEPair E) :
    (fun x : ℝ ↦ P.f x - P.f₀) =O[𝓝[>] 0] (· ^ (-P.k)) := by
  simp_rw [← fun x ↦ sub_add_sub_cancel (P.f x) ((P.ε * ↑(x ^ (-P.k))) • P.g₀) P.f₀]
  refine (P.hf_zero _).add (IsBigO.sub ?_ ?_)
  · rw [← isBigO_norm_norm]
    simp_rw [mul_smul, norm_smul, mul_comm _ ‖P.g₀‖, ← mul_assoc, norm_real]
    apply (isBigO_refl _ _).const_mul_left
  · refine IsBigO.of_bound ‖P.f₀‖ (eventually_nhdsWithin_iff.mpr ?_)
    filter_upwards [eventually_le_nhds zero_lt_one] with x hx' (hx : 0 < x)
    apply le_mul_of_one_le_right (norm_nonneg _)
    rw [norm_of_nonneg (rpow_pos_of_pos hx _).le, rpow_neg hx.le]
    exact (one_le_inv₀ (rpow_pos_of_pos hx _)).2 (rpow_le_one hx.le hx' P.hk.le)

end WeakFEPair

namespace StrongFEPair

variable (P : StrongFEPair E)

lemma hf_top' (r : ℝ) : P.f =O[atTop] (· ^ r) := by
  simpa only [P.hf₀, sub_zero] using P.hf_top r

lemma hf_zero' (r : ℝ) : P.f =O[𝓝[>] 0] (· ^ r) := by
  have := P.hg₀ ▸ P.hf_zero r
  simpa only [smul_zero, sub_zero]

/-!
## Main theorems on strong FE-pairs
-/

def Λ : ℂ → E := mellin P.f

theorem hasMellin (s : ℂ) : HasMellin P.f s (P.Λ s) :=
  let ⟨_, ht⟩ := exists_gt s.re
  let ⟨_, hu⟩ := exists_lt s.re
  ⟨mellinConvergent_of_isBigO_rpow P.hf_int (P.hf_top' _) ht (P.hf_zero' _) hu, rfl⟩

lemma Λ_eq : P.Λ = mellin P.f := rfl

lemma symm_Λ_eq : P.symm.Λ = mellin P.g := rfl

theorem differentiable_Λ : Differentiable ℂ P.Λ := fun s ↦
  let ⟨_, ht⟩ := exists_gt s.re
  let ⟨_, hu⟩ := exists_lt s.re
  mellin_differentiableAt_of_isBigO_rpow P.hf_int (P.hf_top' _) ht (P.hf_zero' _) hu

theorem functional_equation (s : ℂ) :
    P.Λ (P.k - s) = P.ε • P.symm.Λ s := by
  -- unfold definition:
  rw [P.Λ_eq, P.symm_Λ_eq]
  -- substitute `t ↦ t⁻¹` in `mellin P.g s`
  have step1 := mellin_comp_rpow P.g (-s) (-1)
  simp_rw [abs_neg, abs_one, inv_one, one_smul, ofReal_neg, ofReal_one, div_neg, div_one, neg_neg,
    rpow_neg_one, ← one_div] at step1
  -- introduce a power of `t` to match the hypothesis `P.h_feq`
  have step2 := mellin_cpow_smul (fun t ↦ P.g (1 / t)) (P.k - s) (-P.k)
  rw [← sub_eq_add_neg, sub_right_comm, sub_self, zero_sub, step1] at step2
  -- put in the constant `P.ε`
  have step3 := mellin_const_smul (fun t ↦ (t : ℂ) ^ (-P.k : ℂ) • P.g (1 / t)) (P.k - s) P.ε
  rw [step2] at step3
  rw [← step3]
  -- now the integrand matches `P.h_feq'` on `Ioi 0`, so we can apply `setIntegral_congr_fun`
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht ↦ ?_)
  simp_rw [P.h_feq' t ht, ← mul_smul]
  -- some simple `cpow` arithmetic to finish
  rw [cpow_neg, ofReal_cpow (le_of_lt ht)]
  have : (t : ℂ) ^ (P.k : ℂ) ≠ 0 := by
    simpa only [← ofReal_cpow (le_of_lt ht), ofReal_ne_zero] using (rpow_pos_of_pos ht _).ne'
  field_simp [P.hε]

end StrongFEPair

namespace WeakFEPair

variable (P : WeakFEPair E)

/-!
## Auxiliary results II: building a strong FE-pair from a weak FE-pair
-/

def f_modif : ℝ → E :=
  (Ioi 1).indicator (fun x ↦ P.f x - P.f₀) +
  (Ioo 0 1).indicator (fun x ↦ P.f x - (P.ε * ↑(x ^ (-P.k))) • P.g₀)

def g_modif : ℝ → E :=
  (Ioi 1).indicator (fun x ↦ P.g x - P.g₀) +
  (Ioo 0 1).indicator (fun x ↦ P.g x - (P.ε⁻¹ * ↑(x ^ (-P.k))) • P.f₀)

lemma hf_modif_int :
    LocallyIntegrableOn P.f_modif (Ioi 0) := by
  have : LocallyIntegrableOn (fun x : ℝ ↦ (P.ε * ↑(x ^ (-P.k))) • P.g₀) (Ioi 0) := by
    refine ContinuousOn.locallyIntegrableOn ?_ measurableSet_Ioi
    refine continuousOn_of_forall_continuousAt (fun x (hx : 0 < x) ↦ ?_)
    refine (continuousAt_const.mul ?_).smul continuousAt_const
    exact continuous_ofReal.continuousAt.comp (continuousAt_rpow_const _ _ (Or.inl hx.ne'))
  refine LocallyIntegrableOn.add (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · obtain ⟨s, hs, hs'⟩ := P.hf_int.sub (locallyIntegrableOn_const _) x hx
    refine ⟨s, hs, ?_⟩
    rw [IntegrableOn, integrable_indicator_iff measurableSet_Ioi, IntegrableOn,
      Measure.restrict_restrict measurableSet_Ioi, ← IntegrableOn]
    exact hs'.mono_set Set.inter_subset_right
  · obtain ⟨s, hs, hs'⟩ := P.hf_int.sub this x hx
    refine ⟨s, hs, ?_⟩
    rw [IntegrableOn, integrable_indicator_iff measurableSet_Ioo, IntegrableOn,
      Measure.restrict_restrict measurableSet_Ioo, ← IntegrableOn]
    exact hs'.mono_set Set.inter_subset_right

lemma hf_modif_FE (x : ℝ) (hx : 0 < x) :
    P.f_modif (1 / x) = (P.ε * ↑(x ^ P.k)) • P.g_modif x := by
  rcases lt_trichotomy 1 x with hx' | rfl | hx'
  · have : 1 / x < 1 := by rwa [one_div_lt hx one_pos, div_one]
    rw [f_modif, Pi.add_apply, indicator_of_not_mem (not_mem_Ioi.mpr this.le),
      zero_add, indicator_of_mem (mem_Ioo.mpr ⟨div_pos one_pos hx, this⟩), g_modif, Pi.add_apply,
      indicator_of_mem (mem_Ioi.mpr hx'), indicator_of_not_mem
      (not_mem_Ioo_of_ge hx'.le), add_zero, P.h_feq _ hx, smul_sub]
    simp_rw [rpow_neg (one_div_pos.mpr hx).le, one_div, inv_rpow hx.le, inv_inv]
  · simp [f_modif, g_modif]
  · have : 1 < 1 / x := by rwa [lt_one_div one_pos hx, div_one]
    rw [f_modif, Pi.add_apply, indicator_of_mem (mem_Ioi.mpr this),
      indicator_of_not_mem (not_mem_Ioo_of_ge this.le), add_zero, g_modif, Pi.add_apply,
      indicator_of_not_mem (not_mem_Ioi.mpr hx'.le),
      indicator_of_mem (mem_Ioo.mpr ⟨hx, hx'⟩), zero_add, P.h_feq _ hx, smul_sub]
    simp_rw [rpow_neg hx.le, ← mul_smul]
    field_simp [(rpow_pos_of_pos hx P.k).ne', P.hε]

def toStrongFEPair : StrongFEPair E where
  hf_int   := P.hf_modif_int
  hg_int   := P.symm.hf_modif_int
  h_feq    := P.hf_modif_FE
  hε       := P.hε
  hk       := P.hk
  hf₀      := rfl
  hg₀      := rfl
  hf_top r := by
    refine (P.hf_top r).congr' ?_ (by rfl)
    filter_upwards [eventually_gt_atTop 1] with x hx
    rw [f_modif, Pi.add_apply, indicator_of_mem (mem_Ioi.mpr hx),
      indicator_of_not_mem (not_mem_Ioo_of_ge hx.le), add_zero, sub_zero]
  hg_top r := by
    refine (P.hg_top r).congr' ?_ (by rfl)
    filter_upwards [eventually_gt_atTop 1] with x hx
    rw [f_modif, Pi.add_apply, indicator_of_mem (mem_Ioi.mpr hx),
      indicator_of_not_mem (not_mem_Ioo_of_ge hx.le), add_zero, sub_zero]
    rfl

lemma f_modif_aux1 : EqOn (fun x ↦ P.f_modif x - P.f x + P.f₀)
    ((Ioo 0 1).indicator (fun x : ℝ ↦ P.f₀ - (P.ε * ↑(x ^ (-P.k))) • P.g₀)
    + ({1} : Set ℝ).indicator (fun _ ↦ P.f₀ - P.f 1)) (Ioi 0) := by
  intro x (hx : 0 < x)
  simp_rw [f_modif, Pi.add_apply]
  rcases lt_trichotomy x 1 with hx' | rfl | hx'
  · simp_rw [indicator_of_not_mem (not_mem_Ioi.mpr hx'.le),
      indicator_of_mem (mem_Ioo.mpr ⟨hx, hx'⟩),
      indicator_of_not_mem (mem_singleton_iff.not.mpr hx'.ne)]
    abel
  · simp [add_comm, sub_eq_add_neg]
  · simp_rw [indicator_of_mem (mem_Ioi.mpr hx'),
      indicator_of_not_mem (not_mem_Ioo_of_ge hx'.le),
      indicator_of_not_mem (mem_singleton_iff.not.mpr hx'.ne')]
    abel

lemma f_modif_aux2 [CompleteSpace E] {s : ℂ} (hs : P.k < re s) :
    mellin (fun x ↦ P.f_modif x - P.f x + P.f₀) s = (1 / s) • P.f₀ + (P.ε  / (P.k - s)) • P.g₀ := by
  have h_re1 : -1 < re (s - 1) := by simpa using P.hk.trans hs
  have h_re2 : -1 < re (s - P.k - 1) := by simpa using hs
  calc
  _ = ∫ (x : ℝ) in Ioi 0, (x : ℂ) ^ (s - 1) •
      ((Ioo 0 1).indicator (fun t : ℝ ↦ P.f₀ - (P.ε * ↑(t ^ (-P.k))) • P.g₀) x
      + ({1} : Set ℝ).indicator (fun _ ↦ P.f₀ - P.f 1) x) :=
    setIntegral_congr_fun measurableSet_Ioi (fun x hx ↦ by simp [f_modif_aux1 P hx])
  _ = ∫ (x : ℝ) in Ioi 0, (x : ℂ) ^ (s - 1) • ((Ioo 0 1).indicator
      (fun t : ℝ ↦ P.f₀ - (P.ε * ↑(t ^ (-P.k))) • P.g₀) x) := by
    refine setIntegral_congr_ae measurableSet_Ioi (eventually_of_mem (U := {1}ᶜ)
        (compl_mem_ae_iff.mpr (subsingleton_singleton.measure_zero _)) (fun x hx _ ↦ ?_))
    rw [indicator_of_not_mem hx, add_zero]
  _ = ∫ (x : ℝ) in Ioc 0 1, (x : ℂ) ^ (s - 1) • (P.f₀ - (P.ε * ↑(x ^ (-P.k))) • P.g₀) := by
    simp_rw [← indicator_smul, setIntegral_indicator measurableSet_Ioo,
      inter_eq_right.mpr Ioo_subset_Ioi_self, integral_Ioc_eq_integral_Ioo]
  _ = ∫ x : ℝ in Ioc 0 1, ((x : ℂ) ^ (s - 1) • P.f₀ - P.ε • (x : ℂ) ^ (s - P.k - 1) • P.g₀) := by
    refine setIntegral_congr_fun measurableSet_Ioc (fun x ⟨hx, _⟩ ↦ ?_)
    rw [ofReal_cpow hx.le, ofReal_neg, smul_sub, ← mul_smul, mul_comm, mul_assoc, mul_smul,
      mul_comm, ← cpow_add _ _ (ofReal_ne_zero.mpr hx.ne'), ← sub_eq_add_neg, sub_right_comm]
  _ = (∫ (x : ℝ) in Ioc 0 1, (x : ℂ) ^ (s - 1)) • P.f₀
        - P.ε • (∫ (x : ℝ) in Ioc 0 1, (x : ℂ) ^ (s - P.k - 1)) • P.g₀ := by
    rw [integral_sub, integral_smul, integral_smul_const, integral_smul_const]
    · apply Integrable.smul_const
      rw [← IntegrableOn, ← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
      exact intervalIntegral.intervalIntegrable_cpow' h_re1
    · refine (Integrable.smul_const ?_ _).smul _
      rw [← IntegrableOn, ← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
      exact intervalIntegral.intervalIntegrable_cpow' h_re2
  _ = _ := by simp_rw [← intervalIntegral.integral_of_le zero_le_one,
      integral_cpow (Or.inl h_re1), integral_cpow (Or.inl h_re2), ofReal_zero, ofReal_one,
      one_cpow, sub_add_cancel, zero_cpow fun h ↦ lt_irrefl _ (P.hk.le.trans_lt (zero_re ▸ h ▸ hs)),
      zero_cpow (sub_ne_zero.mpr (fun h ↦ lt_irrefl _ ((ofReal_re _) ▸ h ▸ hs)) : s - P.k ≠ 0),
      sub_zero, sub_eq_add_neg (_ •  _), ← mul_smul, ← neg_smul, mul_one_div, ← div_neg, neg_sub]

/-!
## Main theorems on weak FE-pairs
-/

def Λ₀ : ℂ → E := mellin P.f_modif

def Λ (s : ℂ) : E := P.Λ₀ s - (1 / s) • P.f₀ - (P.ε / (P.k - s)) • P.g₀

lemma Λ₀_eq (s : ℂ) : P.Λ₀ s = P.Λ s + (1 / s) • P.f₀ + (P.ε / (P.k - s)) • P.g₀ := by
  unfold Λ Λ₀
  abel

lemma symm_Λ₀_eq (s : ℂ) :
    P.symm.Λ₀ s = P.symm.Λ s + (1 / s) • P.g₀ + (P.ε⁻¹ / (P.k - s)) • P.f₀ := by
  rw [P.symm.Λ₀_eq]
  rfl

theorem differentiable_Λ₀ : Differentiable ℂ P.Λ₀ := P.toStrongFEPair.differentiable_Λ

-- DISSOLVED: differentiableAt_Λ

theorem hasMellin [CompleteSpace E]
    {s : ℂ} (hs : P.k < s.re) : HasMellin (P.f · - P.f₀) s (P.Λ s) := by
  have hc1 : MellinConvergent (P.f · - P.f₀) s :=
    let ⟨_, ht⟩ := exists_gt s.re
    mellinConvergent_of_isBigO_rpow (P.hf_int.sub (locallyIntegrableOn_const _)) (P.hf_top _) ht
      P.hf_zero' hs
  refine ⟨hc1, ?_⟩
  have hc2 : HasMellin P.f_modif s (P.Λ₀ s) := P.toStrongFEPair.hasMellin s
  have hc3 : mellin (fun x ↦ f_modif P x - f P x + P.f₀) s =
    (1 / s) • P.f₀ + (P.ε / (↑P.k - s)) • P.g₀ := P.f_modif_aux2 hs
  have := (hasMellin_sub hc2.1 hc1).2
  simp_rw [← sub_add, hc3, eq_sub_iff_add_eq, ← eq_sub_iff_add_eq', ← sub_sub] at this
  exact this

theorem functional_equation₀ (s : ℂ) : P.Λ₀ (P.k - s) = P.ε • P.symm.Λ₀ s :=
  P.toStrongFEPair.functional_equation s

theorem functional_equation (s : ℂ) :
    P.Λ (P.k - s) = P.ε • P.symm.Λ s := by
  linear_combination (norm := module) P.functional_equation₀ s - P.Λ₀_eq (P.k - s)
    + congr(P.ε • $(P.symm_Λ₀_eq s)) + congr(($(mul_inv_cancel₀ P.hε) / ((P.k:ℂ) - s)) • P.f₀)

theorem Λ_residue_k :
    Tendsto (fun s : ℂ ↦ (s - P.k) • P.Λ s) (𝓝[≠] P.k) (𝓝 (P.ε • P.g₀)) := by
  simp_rw [Λ, smul_sub, (by simp : 𝓝 (P.ε • P.g₀) = 𝓝 (0 - 0 - -P.ε • P.g₀))]
  refine ((Tendsto.sub ?_ ?_).mono_left nhdsWithin_le_nhds).sub ?_
  · rw [(by rw [sub_self, zero_smul] : 𝓝 0 = 𝓝 ((P.k - P.k : ℂ) • P.Λ₀ P.k))]
    apply ((continuous_sub_right _).smul P.differentiable_Λ₀.continuous).tendsto
  · rw [(by rw [sub_self, zero_smul] : 𝓝 0 = 𝓝 ((P.k - P.k : ℂ) • (1 / P.k : ℂ) • P.f₀))]
    refine (continuous_sub_right _).continuousAt.smul (ContinuousAt.smul ?_ continuousAt_const)
    exact continuousAt_const.div continuousAt_id (ofReal_ne_zero.mpr P.hk.ne')
  · refine (tendsto_const_nhds.mono_left nhdsWithin_le_nhds).congr' ?_
    refine eventually_nhdsWithin_of_forall (fun s (hs : s ≠ P.k) ↦ ?_)
    match_scalars
    field_simp [sub_ne_zero.mpr hs.symm]
    ring

theorem Λ_residue_zero :
    Tendsto (fun s : ℂ ↦ s • P.Λ s) (𝓝[≠] 0) (𝓝 (-P.f₀)) := by
  simp_rw [Λ, smul_sub, (by simp : 𝓝 (-P.f₀) = 𝓝 (((0 : ℂ) • P.Λ₀ 0) - P.f₀ - 0))]
  refine ((Tendsto.mono_left ?_ nhdsWithin_le_nhds).sub ?_).sub ?_
  · exact (continuous_id.smul P.differentiable_Λ₀.continuous).tendsto _
  · refine (tendsto_const_nhds.mono_left nhdsWithin_le_nhds).congr' ?_
    refine eventually_nhdsWithin_of_forall (fun s (hs : s ≠ 0) ↦ ?_)
    match_scalars
    field_simp [sub_ne_zero.mpr hs.symm]
  · rw [show 𝓝 0 = 𝓝 ((0 : ℂ) • (P.ε / (P.k - 0 : ℂ)) • P.g₀) by rw [zero_smul]]
    exact (continuousAt_id.smul ((continuousAt_const.div ((continuous_sub_left _).continuousAt)
      (by simpa using P.hk.ne')).smul continuousAt_const)).mono_left nhdsWithin_le_nhds

end WeakFEPair
