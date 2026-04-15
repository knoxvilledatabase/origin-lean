/-
Extracted from NumberTheory/LSeries/Injectivity.lean
Genuine: 7 of 12 | Dissolved: 3 | Infrastructure: 2
-/
import Origin.Core

/-!
# A converging L-series determines its coefficients

We show that two functions `f` and `g : ℕ → ℂ` whose L-series agree and both converge somewhere
must agree on all nonzero arguments. See `LSeries_eq_iff_of_abscissaOfAbsConv_lt_top`
and `LSeries_injOn`.
-/

open LSeries Complex

lemma LSeries.abscissaOfAbsConv_add_le (f g : ℕ → ℂ) :
    abscissaOfAbsConv (f + g) ≤ max (abscissaOfAbsConv f) (abscissaOfAbsConv g) :=
  abscissaOfAbsConv_binop_le LSeriesSummable.add f g

lemma LSeries.abscissaOfAbsConv_sub_le (f g : ℕ → ℂ) :
    abscissaOfAbsConv (f - g) ≤ max (abscissaOfAbsConv f) (abscissaOfAbsConv g) :=
  abscissaOfAbsConv_binop_le LSeriesSummable.sub f g

private

lemma cpow_mul_div_cpow_eq_div_div_cpow (m n : ℕ) (z : ℂ) (x : ℝ) :
    (n + 1) ^ (x : ℂ) * (z / m ^ (x : ℂ)) = z / (m / (n + 1)) ^ (x : ℂ) := by
  have Hn : (0 : ℝ) ≤ (n + 1 : ℝ)⁻¹ := by positivity
  rw [← mul_div_assoc, mul_comm, div_eq_mul_inv z, mul_div_assoc]
  congr
  simp_rw [div_eq_mul_inv]
  rw [show (n + 1 : ℂ)⁻¹ = (n + 1 : ℝ)⁻¹ by simp,
    show (n + 1 : ℂ) = (n + 1 : ℝ) by norm_cast, show (m : ℂ) = (m : ℝ) by norm_cast,
    mul_cpow_ofReal_nonneg m.cast_nonneg Hn, mul_inv, mul_comm]
  congr
  rw [← cpow_neg, show (-x : ℂ) = (-1 : ℝ) * x by simp, cpow_mul_ofReal_nonneg Hn,
    Real.rpow_neg_one, inv_inv]

open Filter Real in

lemma LSeries.tendsto_cpow_mul_atTop {f : ℕ → ℂ} {n : ℕ} (h : ∀ m ≤ n, f m = 0)
    (ha : abscissaOfAbsConv f < ⊤) :
    Tendsto (fun x : ℝ ↦ (n + 1) ^ (x : ℂ) * LSeries f x) atTop (nhds (f (n + 1))) := by
  obtain ⟨y, hay, hyt⟩ := exists_between ha
  lift y to ℝ using ⟨hyt.ne, ((OrderBot.bot_le _).trans_lt hay).ne'⟩
  -- `F x m` is the `m`th term of `(n+1)^x * LSeries f x`, except that `F x (n+1) = 0`
  let F := fun (x : ℝ) ↦ {m | n + 1 < m}.indicator (fun m ↦ f m / (m / (n + 1) : ℂ) ^ (x : ℂ))
  have hF₀ (x : ℝ) {m : ℕ} (hm : m ≤ n + 1) : F x m = 0 := by simp [F, not_lt_of_ge hm]
  have hF (x : ℝ) {m : ℕ} (hm : m ≠ n + 1) : F x m = ((n + 1) ^ (x : ℂ)) * term f x m := by
    rcases lt_trichotomy m (n + 1) with H | rfl | H
    · simp [Nat.not_lt_of_gt H, term, h m <| Nat.lt_succ_iff.mp H, F]
    · exact (hm rfl).elim
    · simp [H, term, (n.zero_lt_succ.trans H).ne', F, cpow_mul_div_cpow_eq_div_div_cpow]
  have hs {x : ℝ} (hx : x ≥ y) : Summable fun m ↦ (n + 1) ^ (x : ℂ) * term f x m := by
    refine (summable_mul_left_iff <| natCast_add_one_cpow_ne_zero n _).mpr <|
       LSeriesSummable_of_abscissaOfAbsConv_lt_re ?_
    simpa only [ofReal_re] using hay.trans_le <| EReal.coe_le_coe_iff.mpr hx
  -- we can write `(n+1)^x * LSeries f x` as `f (n+1)` plus the series over `F x`
  have key : ∀ x ≥ y, (n + 1) ^ (x : ℂ) * LSeries f x = f (n + 1) + ∑' m : ℕ, F x m := by
    intro x hx
    rw [LSeries, ← tsum_mul_left, (hs hx).tsum_eq_add_tsum_ite (n + 1), pow_mul_term_eq f x n]
    congr
    ext1 m
    rcases eq_or_ne m (n + 1) with rfl | hm
    · simp [hF₀ x le_rfl]
    · simp [hm, hF]
  -- reduce to showing that `∑' m, F x m → 0` as `x → ∞`
  conv => enter [3, 1]; rw [← add_zero (f _)]
  refine Tendsto.congr'
    (eventuallyEq_of_mem (s := {x | y ≤ x}) (mem_atTop y) key).symm <| tendsto_const_nhds.add ?_
  -- get the prerequisites for applying dominated convergence
  have hys : Summable (F y) := by
    refine ((hs le_rfl).indicator {m | n + 1 < m}).congr fun m ↦ ?_
    by_cases! hm : n + 1 < m
    · simp [hF, hm, hm.ne']
    · simp [hm, hF₀ _ hm]
  have hc (k : ℕ) : Tendsto (F · k) atTop (nhds 0) := by
    rcases lt_or_ge (n + 1) k with H | H
    · have H₀ : (0 : ℝ) ≤ k / (n + 1) := by positivity
      have H₀' : (0 : ℝ) ≤ (n + 1) / k := by positivity
      have H₁ : (k / (n + 1) : ℂ) = (k / (n + 1) : ℝ) := by push_cast; rfl
      have H₂ : (n + 1) / k < (1 : ℝ) :=
        (div_lt_one <| mod_cast n.succ_pos.trans H).mpr <| mod_cast H
      simp only [Set.mem_setOf_eq, H, Set.indicator_of_mem, F]
      conv =>
        enter [1, x]
        rw [div_eq_mul_inv, H₁, ← ofReal_cpow H₀, ← ofReal_inv, ← Real.inv_rpow H₀, inv_div]
      conv => enter [3, 1]; rw [← mul_zero (f k)]
      exact
        (tendsto_rpow_atTop_of_base_lt_one _ (neg_one_lt_zero.trans_le H₀') H₂).ofReal.const_mul _
    · simp [hF₀ _ H]
  rw [show (0 : ℂ) = tsum (fun _ : ℕ ↦ 0) from tsum_zero.symm]
  refine tendsto_tsum_of_dominated_convergence hys.norm hc <| eventually_iff.mpr ?_
  filter_upwards [mem_atTop y] with y' hy' k
  -- it remains to show that `‖F y' k‖ ≤ ‖F y k‖` (for `y' ≥ y`)
  rcases lt_or_ge (n + 1) k with H | H
  · simp only [Set.mem_setOf_eq, H, Set.indicator_of_mem, norm_div, norm_cpow_real,
      Complex.norm_natCast, F]
    rw [← Nat.cast_one, ← Nat.cast_add, Complex.norm_natCast]
    have hkn : 1 ≤ (k / (n + 1 :) : ℝ) :=
      (one_le_div (by positivity)).mpr <| mod_cast Nat.le_of_succ_le H
    gcongr
  · simp [hF₀ _ H]

open Filter in

lemma LSeries_eq_zero_of_abscissaOfAbsConv_eq_top {f : ℕ → ℂ} (h : abscissaOfAbsConv f = ⊤) :
    LSeries f = 0 := by
  ext1 s
  exact LSeries.eq_zero_of_not_LSeriesSummable f s <| mt LSeriesSummable.abscissaOfAbsConv_le <|
    h ▸ fun H ↦ (H.trans_lt <| EReal.coe_lt_top _).false

open Filter Nat in

-- DISSOLVED: LSeries_eventually_eq_zero_iff'

open Nat in

lemma LSeries_eq_zero_iff {f : ℕ → ℂ} (hf : f 0 = 0) :
    LSeries f = 0 ↔ f = 0 ∨ abscissaOfAbsConv f = ⊤ := by
  by_cases h : abscissaOfAbsConv f = ⊤
  · simpa [h] using LSeries_eq_zero_of_abscissaOfAbsConv_eq_top h
  · simp only [h, or_false]
    refine ⟨fun H ↦ ?_, fun H ↦ H ▸ LSeries_zero⟩
    convert (LSeries_eventually_eq_zero_iff'.mp ?_).resolve_right h
    · refine ⟨fun H' _ _ ↦ by rw [H', Pi.zero_apply], fun H' ↦ ?_⟩
      ext (- | m)
      · simp [hf]
      · simp [H']
    · simpa only [H] using Filter.EventuallyEq.rfl

open Filter in

open Filter in

-- DISSOLVED: LSeries.eq_of_LSeries_eventually_eq

-- DISSOLVED: LSeries_eq_iff_of_abscissaOfAbsConv_lt_top

lemma LSeries_injOn : Set.InjOn LSeries {f | f 0 = 0 ∧ abscissaOfAbsConv f < ⊤} := by
  intro f hf g hg h
  push _ ∈ _ at hf hg
  replace h := (LSeries_eq_iff_of_abscissaOfAbsConv_lt_top hf.2 hg.2).mp h
  ext1 n
  cases n with
  | zero => exact hf.1.trans hg.1.symm
  | succ n => exact h _ n.zero_ne_add_one.symm
