/-
Extracted from Analysis/SpecialFunctions/Pow/Continuity.lean
Genuine: 22 | Conflates: 0 | Dissolved: 33 | Infrastructure: 1
-/
import Origin.Core
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Continuity of power functions

This file contains lemmas about continuity of the power functions on `ℂ`, `ℝ`, `ℝ≥0`, and `ℝ≥0∞`.
-/

noncomputable section

open scoped Classical

open Real Topology NNReal ENNReal Filter ComplexConjugate

open Filter Finset Set

section CpowLimits

/-!
## Continuity for complex powers
-/

open Complex

variable {α : Type*}

-- DISSOLVED: zero_cpow_eq_nhds

-- DISSOLVED: cpow_eq_nhds

-- DISSOLVED: cpow_eq_nhds'

-- DISSOLVED: continuousAt_const_cpow

-- DISSOLVED: continuousAt_const_cpow'

theorem continuousAt_cpow {p : ℂ × ℂ} (hp_fst : p.fst ∈ slitPlane) :
    ContinuousAt (fun x : ℂ × ℂ => x.1 ^ x.2) p := by
  rw [continuousAt_congr (cpow_eq_nhds' <| slitPlane_ne_zero hp_fst)]
  refine continuous_exp.continuousAt.comp ?_
  exact
    ContinuousAt.mul
      (ContinuousAt.comp (continuousAt_clog hp_fst) continuous_fst.continuousAt)
      continuous_snd.continuousAt

theorem continuousAt_cpow_const {a b : ℂ} (ha : a ∈ slitPlane) :
    ContinuousAt (· ^ b) a :=
  Tendsto.comp (@continuousAt_cpow (a, b) ha) (continuousAt_id.prod continuousAt_const)

theorem Filter.Tendsto.cpow {l : Filter α} {f g : α → ℂ} {a b : ℂ} (hf : Tendsto f l (𝓝 a))
    (hg : Tendsto g l (𝓝 b)) (ha : a ∈ slitPlane) :
    Tendsto (fun x => f x ^ g x) l (𝓝 (a ^ b)) :=
  (@continuousAt_cpow (a, b) ha).tendsto.comp (hf.prod_mk_nhds hg)

-- DISSOLVED: Filter.Tendsto.const_cpow

variable [TopologicalSpace α] {f g : α → ℂ} {s : Set α} {a : α}

nonrec theorem ContinuousWithinAt.cpow (hf : ContinuousWithinAt f s a)
    (hg : ContinuousWithinAt g s a) (h0 : f a ∈ slitPlane) :
    ContinuousWithinAt (fun x => f x ^ g x) s a :=
  hf.cpow hg h0

-- DISSOLVED: ContinuousWithinAt.const_cpow

nonrec theorem ContinuousAt.cpow (hf : ContinuousAt f a) (hg : ContinuousAt g a)
    (h0 : f a ∈ slitPlane) : ContinuousAt (fun x => f x ^ g x) a :=
  hf.cpow hg h0

-- DISSOLVED: ContinuousAt.const_cpow

theorem ContinuousOn.cpow (hf : ContinuousOn f s) (hg : ContinuousOn g s)
    (h0 : ∀ a ∈ s, f a ∈ slitPlane) : ContinuousOn (fun x => f x ^ g x) s := fun a ha =>
  (hf a ha).cpow (hg a ha) (h0 a ha)

-- DISSOLVED: ContinuousOn.const_cpow

theorem Continuous.cpow (hf : Continuous f) (hg : Continuous g)
    (h0 : ∀ a, f a ∈ slitPlane) : Continuous fun x => f x ^ g x :=
  continuous_iff_continuousAt.2 fun a => hf.continuousAt.cpow hg.continuousAt (h0 a)

-- DISSOLVED: Continuous.const_cpow

theorem ContinuousOn.cpow_const {b : ℂ} (hf : ContinuousOn f s)
    (h : ∀ a : α, a ∈ s → f a ∈ slitPlane) : ContinuousOn (fun x => f x ^ b) s :=
  hf.cpow continuousOn_const h

-- DISSOLVED: continuous_const_cpow

end CpowLimits

section RpowLimits

/-!
## Continuity for real powers
-/

namespace Real

-- DISSOLVED: continuousAt_const_rpow

-- DISSOLVED: continuousAt_const_rpow'

theorem rpow_eq_nhds_of_neg {p : ℝ × ℝ} (hp_fst : p.fst < 0) :
    (fun x : ℝ × ℝ => x.1 ^ x.2) =ᶠ[𝓝 p] fun x => exp (log x.1 * x.2) * cos (x.2 * π) := by
  suffices ∀ᶠ x : ℝ × ℝ in 𝓝 p, x.1 < 0 from
    this.mono fun x hx ↦ by
      dsimp only
      rw [rpow_def_of_neg hx]
  exact IsOpen.eventually_mem (isOpen_lt continuous_fst continuous_const) hp_fst

theorem rpow_eq_nhds_of_pos {p : ℝ × ℝ} (hp_fst : 0 < p.fst) :
    (fun x : ℝ × ℝ => x.1 ^ x.2) =ᶠ[𝓝 p] fun x => exp (log x.1 * x.2) := by
  suffices ∀ᶠ x : ℝ × ℝ in 𝓝 p, 0 < x.1 from
    this.mono fun x hx ↦ by
      dsimp only
      rw [rpow_def_of_pos hx]
  exact IsOpen.eventually_mem (isOpen_lt continuous_const continuous_fst) hp_fst

-- DISSOLVED: continuousAt_rpow_of_ne

theorem continuousAt_rpow_of_pos (p : ℝ × ℝ) (hp : 0 < p.2) :
    ContinuousAt (fun p : ℝ × ℝ => p.1 ^ p.2) p := by
  cases' p with x y
  dsimp only at hp
  obtain hx | rfl := ne_or_eq x 0
  · exact continuousAt_rpow_of_ne (x, y) hx
  have A : Tendsto (fun p : ℝ × ℝ => exp (log p.1 * p.2)) (𝓝[≠] 0 ×ˢ 𝓝 y) (𝓝 0) :=
    tendsto_exp_atBot.comp
      ((tendsto_log_nhdsWithin_zero.comp tendsto_fst).atBot_mul hp tendsto_snd)
  have B : Tendsto (fun p : ℝ × ℝ => p.1 ^ p.2) (𝓝[≠] 0 ×ˢ 𝓝 y) (𝓝 0) :=
    squeeze_zero_norm (fun p => abs_rpow_le_exp_log_mul p.1 p.2) A
  have C : Tendsto (fun p : ℝ × ℝ => p.1 ^ p.2) (𝓝[{0}] 0 ×ˢ 𝓝 y) (pure 0) := by
    rw [nhdsWithin_singleton, tendsto_pure, pure_prod, eventually_map]
    exact (lt_mem_nhds hp).mono fun y hy => zero_rpow hy.ne'
  simpa only [← sup_prod, ← nhdsWithin_union, compl_union_self, nhdsWithin_univ, nhds_prod_eq,
    ContinuousAt, zero_rpow hp.ne'] using B.sup (C.mono_right (pure_le_nhds _))

-- DISSOLVED: continuousAt_rpow

-- DISSOLVED: continuousAt_rpow_const

· rw [le_iff_lt_or_eq, ← or_assoc] at h

  obtain h|rfl := h

  · exact (continuousAt_rpow (x, q) h).comp₂ continuousAt_id continuousAt_const

  · simp_rw [rpow_zero]; exact continuousAt_const

@[fun_prop]
theorem continuous_rpow_const {q : ℝ} (h : 0 ≤ q) : Continuous (fun x : ℝ => x ^ q) :=
  continuous_iff_continuousAt.mpr fun x ↦ continuousAt_rpow_const x q (.inr h)

end Real

section

variable {α : Type*}

-- DISSOLVED: Filter.Tendsto.rpow

-- DISSOLVED: Filter.Tendsto.rpow_const

variable [TopologicalSpace α] {f g : α → ℝ} {s : Set α} {x : α} {p : ℝ}

-- DISSOLVED: ContinuousAt.rpow

-- DISSOLVED: ContinuousWithinAt.rpow

-- DISSOLVED: ContinuousOn.rpow

-- DISSOLVED: Continuous.rpow

-- DISSOLVED: ContinuousWithinAt.rpow_const

-- DISSOLVED: ContinuousAt.rpow_const

-- DISSOLVED: ContinuousOn.rpow_const

-- DISSOLVED: Continuous.rpow_const

end

end RpowLimits

/-! ## Continuity results for `cpow`, part II

These results involve relating real and complex powers, so cannot be done higher up.
-/

section CpowLimits2

namespace Complex

theorem continuousAt_cpow_zero_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    ContinuousAt (fun x : ℂ × ℂ => x.1 ^ x.2) (0, z) := by
  have hz₀ : z ≠ 0 := ne_of_apply_ne re hz.ne'
  rw [ContinuousAt, zero_cpow hz₀, tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun _ => abs_cpow_le _ _) ?_
  simp only [div_eq_mul_inv, ← Real.exp_neg]
  refine Tendsto.zero_mul_isBoundedUnder_le ?_ ?_
  · convert
        (continuous_fst.norm.tendsto ((0 : ℂ), z)).rpow
          ((continuous_re.comp continuous_snd).tendsto _) _ <;>
      simp [hz, Real.zero_rpow hz.ne']
  · simp only [Function.comp_def, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rcases exists_gt |im z| with ⟨C, hC⟩
    refine ⟨Real.exp (π * C), eventually_map.2 ?_⟩
    refine
      (((continuous_im.comp continuous_snd).abs.tendsto (_, z)).eventually (gt_mem_nhds hC)).mono
        fun z hz => Real.exp_le_exp.2 <| (neg_le_abs _).trans ?_
    rw [_root_.abs_mul]
    exact
      mul_le_mul (abs_le.2 ⟨(neg_pi_lt_arg _).le, arg_le_pi _⟩) hz.le (_root_.abs_nonneg _)
        Real.pi_pos.le

open ComplexOrder in

-- DISSOLVED: continuousAt_cpow_of_re_pos

-- DISSOLVED: continuousAt_cpow_const_of_re_pos

-- DISSOLVED: continuousAt_ofReal_cpow

-- DISSOLVED: continuousAt_ofReal_cpow_const

theorem continuous_ofReal_cpow_const {y : ℂ} (hs : 0 < y.re) :
    Continuous (fun x => (x : ℂ) ^ y : ℝ → ℂ) :=
  continuous_iff_continuousAt.mpr fun x => continuousAt_ofReal_cpow_const x y (Or.inl hs)

end Complex

end CpowLimits2

/-! ## Limits and continuity for `ℝ≥0` powers -/

namespace NNReal

-- DISSOLVED: continuousAt_rpow

theorem eventually_pow_one_div_le (x : ℝ≥0) {y : ℝ≥0} (hy : 1 < y) :
    ∀ᶠ n : ℕ in atTop, x ^ (1 / n : ℝ) ≤ y := by
  obtain ⟨m, hm⟩ := add_one_pow_unbounded_of_pos x (tsub_pos_of_lt hy)
  rw [tsub_add_cancel_of_le hy.le] at hm
  refine eventually_atTop.2 ⟨m + 1, fun n hn => ?_⟩
  simp only [one_div]
  simpa only [NNReal.rpow_inv_le_iff (Nat.cast_pos.2 <| m.succ_pos.trans_le hn),
    NNReal.rpow_natCast] using hm.le.trans (pow_right_mono₀ hy.le (m.le_succ.trans hn))

end NNReal

open Filter

-- DISSOLVED: Filter.Tendsto.nnrpow

namespace NNReal

-- DISSOLVED: continuousAt_rpow_const

@[fun_prop]
theorem continuous_rpow_const {y : ℝ} (h : 0 ≤ y) : Continuous fun x : ℝ≥0 => x ^ y :=
  continuous_iff_continuousAt.2 fun _ => continuousAt_rpow_const (Or.inr h)

@[fun_prop]
theorem continuousOn_rpow_const_compl_zero {r : ℝ} :
    ContinuousOn (fun z : ℝ≥0 => z ^ r) {0}ᶜ :=
  fun _ h => ContinuousAt.continuousWithinAt <| NNReal.continuousAt_rpow_const (.inl h)

@[fun_prop]
theorem continuousOn_rpow_const {r : ℝ} {s : Set ℝ≥0}
    (h : 0 ∉ s ∨ 0 ≤ r) : ContinuousOn (fun z : ℝ≥0 => z ^ r) s :=
  h.elim (fun _ ↦ ContinuousOn.mono (s := {0}ᶜ) (by fun_prop) (by aesop))
    (NNReal.continuous_rpow_const · |>.continuousOn)

end NNReal

/-! ## Continuity for `ℝ≥0∞` powers -/

namespace ENNReal

theorem eventually_pow_one_div_le {x : ℝ≥0∞} (hx : x ≠ ∞) {y : ℝ≥0∞} (hy : 1 < y) :
    ∀ᶠ n : ℕ in atTop, x ^ (1 / n : ℝ) ≤ y := by
  lift x to ℝ≥0 using hx
  by_cases h : y = ∞
  · exact Eventually.of_forall fun n => h.symm ▸ le_top
  · lift y to ℝ≥0 using h
    have := NNReal.eventually_pow_one_div_le x (mod_cast hy : 1 < y)
    refine this.congr (Eventually.of_forall fun n => ?_)
    rw [← coe_rpow_of_nonneg x (by positivity : 0 ≤ (1 / n : ℝ)), coe_le_coe]

private theorem continuousAt_rpow_const_of_pos {x : ℝ≥0∞} {y : ℝ} (h : 0 < y) :
    ContinuousAt (fun a : ℝ≥0∞ => a ^ y) x := by
  by_cases hx : x = ⊤
  · rw [hx, ContinuousAt]
    convert ENNReal.tendsto_rpow_at_top h
    simp [h]
  lift x to ℝ≥0 using hx
  rw [continuousAt_coe_iff]
  convert continuous_coe.continuousAt.comp (NNReal.continuousAt_rpow_const (Or.inr h.le)) using 1
  ext1 x
  simp [← coe_rpow_of_nonneg _ h.le]

@[continuity, fun_prop]
theorem continuous_rpow_const {y : ℝ} : Continuous fun a : ℝ≥0∞ => a ^ y := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  rcases lt_trichotomy (0 : ℝ) y with (hy | rfl | hy)
  · exact continuousAt_rpow_const_of_pos hy
  · simp only [rpow_zero]
    exact continuousAt_const
  · obtain ⟨z, hz⟩ : ∃ z, y = -z := ⟨-y, (neg_neg _).symm⟩
    have z_pos : 0 < z := by simpa [hz] using hy
    simp_rw [hz, rpow_neg]
    exact continuous_inv.continuousAt.comp (continuousAt_rpow_const_of_pos z_pos)

theorem tendsto_const_mul_rpow_nhds_zero_of_pos {c : ℝ≥0∞} (hc : c ≠ ∞) {y : ℝ} (hy : 0 < y) :
    Tendsto (fun x : ℝ≥0∞ => c * x ^ y) (𝓝 0) (𝓝 0) := by
  convert ENNReal.Tendsto.const_mul (ENNReal.continuous_rpow_const.tendsto 0) _
  · simp [hy]
  · exact Or.inr hc

end ENNReal

theorem Filter.Tendsto.ennrpow_const {α : Type*} {f : Filter α} {m : α → ℝ≥0∞} {a : ℝ≥0∞} (r : ℝ)
    (hm : Tendsto m f (𝓝 a)) : Tendsto (fun x => m x ^ r) f (𝓝 (a ^ r)) :=
  (ENNReal.continuous_rpow_const.tendsto a).comp hm
