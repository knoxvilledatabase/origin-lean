/-
Extracted from Analysis/Analytic/IsolatedZeros.lean
Genuine: 17 of 25 | Dissolved: 8 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Principle of isolated zeros

This file proves the fact that the zeros of a non-constant analytic function of one variable are
isolated. It also introduces a little bit of API in the `HasFPowerSeriesAt` namespace that is
useful in this setup.

## Main results

* `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero` is the main statement that if a function is
  analytic at `z₀`, then either it is identically zero in a neighborhood of `z₀`, or it does not
  vanish in a punctured neighborhood of `z₀`.
* `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq` is the identity theorem for analytic
  functions: if a function `f` is analytic on a connected set `U` and is zero on a set with an
  accumulation point in `U` then `f` is identically `0` on `U`.
-/

open scoped Classical

open Filter Function Nat FormalMultilinearSeries EMetric Set

open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {s : E} {p q : FormalMultilinearSeries 𝕜 𝕜 E} {f g : 𝕜 → E} {n : ℕ} {z z₀ : 𝕜}

namespace HasSum

variable {a : ℕ → E}

theorem hasSum_at_zero (a : ℕ → E) : HasSum (fun n => (0 : 𝕜) ^ n • a n) (a 0) := by
  convert hasSum_single (α := E) 0 fun b h ↦ _ <;> simp [*]

theorem exists_hasSum_smul_of_apply_eq_zero (hs : HasSum (fun m => z ^ m • a m) s)
    (ha : ∀ k < n, a k = 0) : ∃ t : E, z ^ n • t = s ∧ HasSum (fun m => z ^ m • a (m + n)) t := by
  obtain rfl | hn := n.eq_zero_or_pos
  · simpa
  by_cases h : z = 0
  · have : s = 0 := hs.unique (by simpa [ha 0 hn, h] using hasSum_at_zero a)
    exact ⟨a n, by simp [h, hn.ne', this], by simpa [h] using hasSum_at_zero fun m => a (m + n)⟩
  · refine ⟨(z ^ n)⁻¹ • s, by field_simp [smul_smul], ?_⟩
    have h1 : ∑ i ∈ Finset.range n, z ^ i • a i = 0 :=
      Finset.sum_eq_zero fun k hk => by simp [ha k (Finset.mem_range.mp hk)]
    have h2 : HasSum (fun m => z ^ (m + n) • a (m + n)) s := by
      simpa [h1] using (hasSum_nat_add_iff' n).mpr hs
    convert h2.const_smul (z⁻¹ ^ n) using 1
    · field_simp [pow_add, smul_smul]
    · simp only [inv_pow]

end HasSum

namespace HasFPowerSeriesAt

theorem has_fpower_series_dslope_fslope (hp : HasFPowerSeriesAt f p z₀) :
    HasFPowerSeriesAt (dslope f z₀) p.fslope z₀ := by
  have hpd : deriv f z₀ = p.coeff 1 := hp.deriv
  have hp0 : p.coeff 0 = f z₀ := hp.coeff_zero 1
  simp only [hasFPowerSeriesAt_iff, apply_eq_pow_smul_coeff, coeff_fslope] at hp ⊢
  refine hp.mono fun x hx => ?_
  by_cases h : x = 0
  · convert hasSum_single (α := E) 0 _ <;> intros <;> simp [*]
  · have hxx : ∀ n : ℕ, x⁻¹ * x ^ (n + 1) = x ^ n := fun n => by field_simp [h, _root_.pow_succ]
    suffices HasSum (fun n => x⁻¹ • x ^ (n + 1) • p.coeff (n + 1)) (x⁻¹ • (f (z₀ + x) - f z₀)) by
      simpa [dslope, slope, h, smul_smul, hxx] using this
    simpa [hp0] using ((hasSum_nat_add_iff' 1).mpr hx).const_smul x⁻¹

theorem has_fpower_series_iterate_dslope_fslope (n : ℕ) (hp : HasFPowerSeriesAt f p z₀) :
    HasFPowerSeriesAt ((swap dslope z₀)^[n] f) (fslope^[n] p) z₀ := by
  induction n generalizing f p with
  | zero => exact hp
  | succ n ih => simpa using ih (has_fpower_series_dslope_fslope hp)

-- DISSOLVED: iterate_dslope_fslope_ne_zero

theorem eq_pow_order_mul_iterate_dslope (hp : HasFPowerSeriesAt f p z₀) :
    ∀ᶠ z in 𝓝 z₀, f z = (z - z₀) ^ p.order • (swap dslope z₀)^[p.order] f z := by
  have hq := hasFPowerSeriesAt_iff'.mp (has_fpower_series_iterate_dslope_fslope p.order hp)
  filter_upwards [hq, hasFPowerSeriesAt_iff'.mp hp] with x hx1 hx2
  have : ∀ k < p.order, p.coeff k = 0 := fun k hk => by
    simpa [coeff_eq_zero] using apply_eq_zero_of_lt_order hk
  obtain ⟨s, hs1, hs2⟩ := HasSum.exists_hasSum_smul_of_apply_eq_zero hx2 this
  convert hs1.symm
  simp only [coeff_iterate_fslope] at hx1
  exact hx1.unique hs2

-- DISSOLVED: locally_ne_zero

theorem locally_zero_iff (hp : HasFPowerSeriesAt f p z₀) : (∀ᶠ z in 𝓝 z₀, f z = 0) ↔ p = 0 :=
  ⟨fun hf => hp.eq_zero_of_eventually hf, fun h => eventually_eq_zero (𝕜 := 𝕜) (by rwa [h] at hp)⟩

end HasFPowerSeriesAt

namespace AnalyticAt

-- DISSOLVED: eventually_eq_zero_or_eventually_ne_zero

theorem eventually_eq_or_eventually_ne (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀) :
    (∀ᶠ z in 𝓝 z₀, f z = g z) ∨ ∀ᶠ z in 𝓝[≠] z₀, f z ≠ g z := by
  simpa [sub_eq_zero] using (hf.sub hg).eventually_eq_zero_or_eventually_ne_zero

theorem frequently_zero_iff_eventually_zero {f : 𝕜 → E} {w : 𝕜} (hf : AnalyticAt 𝕜 f w) :
    (∃ᶠ z in 𝓝[≠] w, f z = 0) ↔ ∀ᶠ z in 𝓝 w, f z = 0 :=
  ⟨hf.eventually_eq_zero_or_eventually_ne_zero.resolve_right, fun h =>
    (h.filter_mono nhdsWithin_le_nhds).frequently⟩

theorem frequently_eq_iff_eventually_eq (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀) :
    (∃ᶠ z in 𝓝[≠] z₀, f z = g z) ↔ ∀ᶠ z in 𝓝 z₀, f z = g z := by
  simpa [sub_eq_zero] using frequently_zero_iff_eventually_zero (hf.sub hg)

-- DISSOLVED: unique_eventuallyEq_zpow_smul_nonzero

-- DISSOLVED: unique_eventuallyEq_pow_smul_nonzero

-- DISSOLVED: exists_eventuallyEq_pow_smul_nonzero_iff

noncomputable def order (hf : AnalyticAt 𝕜 f z₀) : ENat :=
  if h : ∀ᶠ z in 𝓝 z₀, f z = 0 then ⊤
  else ↑(hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr h).choose

lemma order_eq_top_iff (hf : AnalyticAt 𝕜 f z₀) : hf.order = ⊤ ↔ ∀ᶠ z in 𝓝 z₀, f z = 0 := by
  unfold order
  split_ifs with h
  · rwa [eq_self, true_iff]
  · simpa only [ne_eq, ENat.coe_ne_top, false_iff] using h

-- DISSOLVED: order_eq_nat_iff

end AnalyticAt

namespace AnalyticOnNhd

variable {U : Set 𝕜}

theorem eqOn_zero_of_preconnected_of_frequently_eq_zero (hf : AnalyticOnNhd 𝕜 f U)
    (hU : IsPreconnected U) (h₀ : z₀ ∈ U) (hfw : ∃ᶠ z in 𝓝[≠] z₀, f z = 0) : EqOn f 0 U :=
  hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU h₀
    ((hf z₀ h₀).frequently_zero_iff_eventually_zero.1 hfw)

-- DISSOLVED: eqOn_zero_or_eventually_ne_zero_of_preconnected

theorem eqOn_zero_of_preconnected_of_mem_closure (hf : AnalyticOnNhd 𝕜 f U) (hU : IsPreconnected U)
    (h₀ : z₀ ∈ U) (hfz₀ : z₀ ∈ closure ({z | f z = 0} \ {z₀})) : EqOn f 0 U :=
  hf.eqOn_zero_of_preconnected_of_frequently_eq_zero hU h₀
    (mem_closure_ne_iff_frequently_within.mp hfz₀)

theorem eqOn_of_preconnected_of_frequently_eq (hf : AnalyticOnNhd 𝕜 f U) (hg : AnalyticOnNhd 𝕜 g U)
    (hU : IsPreconnected U) (h₀ : z₀ ∈ U) (hfg : ∃ᶠ z in 𝓝[≠] z₀, f z = g z) : EqOn f g U := by
  have hfg' : ∃ᶠ z in 𝓝[≠] z₀, (f - g) z = 0 :=
    hfg.mono fun z h => by rw [Pi.sub_apply, h, sub_self]
  simpa [sub_eq_zero] using fun z hz =>
    (hf.sub hg).eqOn_zero_of_preconnected_of_frequently_eq_zero hU h₀ hfg' hz

theorem eqOn_or_eventually_ne_of_preconnected (hf : AnalyticOnNhd 𝕜 f U) (hg : AnalyticOnNhd 𝕜 g U)
    (hU : IsPreconnected U) : EqOn f g U ∨ ∀ᶠ x in codiscreteWithin U, f x ≠ g x :=
  (eqOn_zero_or_eventually_ne_zero_of_preconnected (hf.sub hg) hU).imp
    (fun h _ hx ↦ eq_of_sub_eq_zero (h hx))
    (by simp only [Pi.sub_apply, ne_eq, sub_eq_zero, imp_self])

theorem eqOn_of_preconnected_of_mem_closure (hf : AnalyticOnNhd 𝕜 f U) (hg : AnalyticOnNhd 𝕜 g U)
    (hU : IsPreconnected U) (h₀ : z₀ ∈ U) (hfg : z₀ ∈ closure ({z | f z = g z} \ {z₀})) :
    EqOn f g U :=
  hf.eqOn_of_preconnected_of_frequently_eq hg hU h₀ (mem_closure_ne_iff_frequently_within.mp hfg)

theorem eq_of_frequently_eq [ConnectedSpace 𝕜] (hf : AnalyticOnNhd 𝕜 f univ)
    (hg : AnalyticOnNhd 𝕜 g univ) (hfg : ∃ᶠ z in 𝓝[≠] z₀, f z = g z) : f = g :=
  funext fun x =>
    eqOn_of_preconnected_of_frequently_eq hf hg isPreconnected_univ (mem_univ z₀) hfg (mem_univ x)

alias _root_.AnalyticOn.eq_of_frequently_eq := eq_of_frequently_eq

end AnalyticOnNhd
