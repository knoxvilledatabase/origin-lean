/-
Extracted from NumberTheory/AbelSummation.lean
Genuine: 8 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.MeasureTheory.Integral.FundThmCalculus

noncomputable section

/-!
# Abel's summation formula

We prove several versions of Abel's summation formula.

## Results

* `sum_mul_eq_sub_sub_integral_mul`: general statement of the formula for a sum between two
(nonnegative) reals `a` and `b`.

* `sum_mul_eq_sub_integral_mul`: a specialized version of `sum_mul_eq_sub_sub_integral_mul` for
  the case `a = 0`.

 * `sum_mul_eq_sub_integral_mul`: a specialized version of `sum_mul_eq_sub_integral_mul` for
  when the first coefficient of the sequence is `0`. This is useful for `ArithmeticFunction`.

## References

* <https://en.wikipedia.org/wiki/Abel%27s_summation_formula>

-/

noncomputable section

open Finset intervalIntegral MeasureTheory IntervalIntegrable

variable {𝕜 : Type*} [RCLike 𝕜] (c : ℕ → 𝕜) {f : ℝ → 𝕜} {a b : ℝ}

namespace abelSummationProof

private theorem sumlocc (n : ℕ) :
    ∀ᵐ t, t ∈ Set.Icc (n : ℝ) (n + 1) → ∑ k ∈ Icc 0 ⌊t⌋₊, c k = ∑ k ∈ Icc 0 n, c k := by
  filter_upwards [Ico_ae_eq_Icc] with t h ht
  rw [Nat.floor_eq_on_Ico _ _ (h.mpr ht)]

private theorem integralmulsum (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (hf_int : IntegrableOn (deriv f) (Set.Icc a b)) (t₁ t₂ : ℝ) (n : ℕ) (h : t₁ ≤ t₂)
    (h₁ : n ≤ t₁) (h₂ : t₂ ≤ n + 1) (h₃ : a ≤ t₁) (h₄ : t₂ ≤ b) :
    ∫ t in t₁..t₂, deriv f t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k =
      (f t₂ - f t₁) * ∑ k ∈ Icc 0 n, c k := by
  have h_inc₁ : Ι t₁ t₂ ⊆ Set.Icc n (n + 1) :=
    Set.uIoc_of_le h ▸ Set.Ioc_subset_Icc_self.trans <| Set.Icc_subset_Icc h₁ h₂
  have h_inc₂ : Set.uIcc t₁ t₂ ⊆ Set.Icc a b := Set.uIcc_of_le h ▸ Set.Icc_subset_Icc h₃ h₄
  rw [← integral_deriv_eq_sub (fun t ht ↦ hf_diff t (h_inc₂ ht)), ← integral_mul_const]
  · refine integral_congr_ae ?_
    filter_upwards [sumlocc c n] with t h h'
    rw [h (h_inc₁ h')]
  · refine (intervalIntegrable_iff_integrableOn_Icc_of_le h).mpr (hf_int.mono_set ?_)
    rwa [← Set.uIcc_of_le h]

private theorem ineqofmemIco {k : ℕ} (hk : k ∈ Set.Ico (⌊a⌋₊ + 1) ⌊b⌋₊) :
    a ≤ k ∧ k + 1 ≤ b := by
  constructor
  · have := (Set.mem_Ico.mp hk).1
    exact le_of_lt <| (Nat.floor_lt' (by omega)).mp this
  · rw [← Nat.cast_add_one, ← Nat.le_floor_iff' (Nat.succ_ne_zero k)]
    exact (Set.mem_Ico.mp hk).2

private theorem ineqofmemIco' {k : ℕ} (hk : k ∈ Ico (⌊a⌋₊ + 1) ⌊b⌋₊) :
    a ≤ k ∧ k + 1 ≤ b :=
  ineqofmemIco (by rwa [← Finset.coe_Ico])

private theorem integrablemulsum (ha : 0 ≤ a) (hb : ⌊a⌋₊ < ⌊b⌋₊)
    (hf_int : IntegrableOn (deriv f) (Set.Icc a b)) :
    IntegrableOn (fun t ↦ deriv f t * (∑ k ∈ Icc 0 ⌊t⌋₊, c k)) (Set.Icc a b) := by
  have h_locint {t₁ t₂ : ℝ} {n : ℕ} (h : t₁ ≤ t₂) (h₁ : n ≤ t₁) (h₂ : t₂ ≤ n + 1)
      (h₃ : a ≤ t₁) (h₄ : t₂ ≤ b) :
      IntervalIntegrable (fun t ↦ deriv f t * (∑ k ∈ Icc 0 ⌊t⌋₊, c k)) volume t₁ t₂ := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le h]
    exact (IntegrableOn.mono_set (hf_int.mul_const _) (Set.Icc_subset_Icc h₃ h₄)).congr
      <| ae_restrict_of_ae_restrict_of_subset (Set.Icc_subset_Icc h₁ h₂)
        <| (ae_restrict_iff' measurableSet_Icc).mpr
          (by filter_upwards [sumlocc c n] with t h ht using by rw [h ht])
  have aux1 : 0 ≤ b := (Nat.pos_of_floor_pos <| (Nat.zero_le _).trans_lt hb).le
  have aux2 : ⌊a⌋₊ + 1 ≤ b := by rwa [← Nat.cast_add_one, ← Nat.le_floor_iff aux1]
  have aux3 : a ≤ ⌊a⌋₊ + 1 := (Nat.lt_floor_add_one _).le
  have aux4 : a ≤ ⌊b⌋₊ := le_of_lt (by rwa [← Nat.floor_lt ha])
  -- now break up into 3 subintervals
  rw [← intervalIntegrable_iff_integrableOn_Icc_of_le (aux3.trans aux2)]
  have I1 : IntervalIntegrable _ volume a ↑(⌊a⌋₊ + 1) :=
    h_locint (mod_cast aux3) (Nat.floor_le ha) (mod_cast le_rfl) le_rfl (mod_cast aux2)
  have I2 : IntervalIntegrable _ volume ↑(⌊a⌋₊ + 1) ⌊b⌋₊ :=
    trans_iterate_Ico hb fun k hk ↦ h_locint (mod_cast k.le_succ)
      le_rfl (mod_cast le_rfl) (ineqofmemIco hk).1 (mod_cast (ineqofmemIco hk).2)
  have I3 : IntervalIntegrable _ volume ⌊b⌋₊ b :=
    h_locint (Nat.floor_le aux1) le_rfl (Nat.lt_floor_add_one _).le aux4 le_rfl
  exact (I1.trans I2).trans I3

theorem _root_.sum_mul_eq_sub_sub_integral_mul (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (hf_int : IntegrableOn (deriv f) (Set.Icc a b)) :
    ∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f k * c k =
      f b * (∑ k ∈ Icc 0 ⌊b⌋₊, c k) - f a * (∑ k ∈ Icc 0 ⌊a⌋₊, c k) -
        ∫ t in Set.Ioc a b, deriv f t * (∑ k ∈ Icc 0 ⌊t⌋₊, c k) := by
  rw [← integral_of_le hab]
  have aux1 : ⌊a⌋₊ ≤ a := Nat.floor_le ha
  have aux2 : b ≤ ⌊b⌋₊ + 1 := (Nat.lt_floor_add_one _).le
  -- We consider two cases depending on whether the sum is empty or not
  obtain hb | hb := eq_or_lt_of_le (Nat.floor_le_floor hab)
  · rw [hb, Ioc_eq_empty_of_le le_rfl, sum_empty, ← sub_mul,
      integralmulsum c hf_diff hf_int _ _ ⌊b⌋₊ hab (hb ▸ aux1) aux2 le_rfl le_rfl, sub_self]
  have aux3 : a ≤ ⌊a⌋₊ + 1 := (Nat.lt_floor_add_one _).le
  have aux4 : ⌊a⌋₊ + 1 ≤ b := by rwa [← Nat.cast_add_one,  ← Nat.le_floor_iff (ha.trans hab)]
  have aux5 : ⌊b⌋₊ ≤ b := Nat.floor_le (ha.trans hab)
  have aux6 : a ≤ ⌊b⌋₊ := Nat.floor_lt ha |>.mp hb |>.le
  simp_rw [← smul_eq_mul, sum_Ioc_by_parts (fun k ↦ f k) _ hb, range_eq_Ico, Nat.Ico_succ_right,
    smul_eq_mul]
  have : ∑ k ∈ Ioc ⌊a⌋₊ (⌊b⌋₊ - 1), (f ↑(k + 1) - f k) * ∑ n ∈ Icc 0 k, c n =
        ∑ k ∈ Ico (⌊a⌋₊ + 1) ⌊b⌋₊, ∫ t in k..↑(k + 1), deriv f t * ∑ n ∈ Icc 0 ⌊t⌋₊, c n := by
    rw [← Nat.Ico_succ_succ, Nat.succ_eq_add_one,  Nat.succ_eq_add_one, Nat.sub_add_cancel
      (by omega), Eq.comm]
    exact sum_congr rfl fun k hk ↦ (integralmulsum c hf_diff hf_int _ _ _  (mod_cast k.le_succ)
      le_rfl (mod_cast le_rfl) (ineqofmemIco' hk).1 <| mod_cast (ineqofmemIco' hk).2)
  rw [this, sum_integral_adjacent_intervals_Ico hb, Nat.cast_add, Nat.cast_one,
    ← integral_interval_sub_left (a := a) (c := ⌊a⌋₊ + 1),
    ← integral_add_adjacent_intervals (b := ⌊b⌋₊) (c := b),
    integralmulsum c hf_diff hf_int _ _ _ aux3 aux1 le_rfl le_rfl aux4,
    integralmulsum c hf_diff hf_int _ _ _ aux5 le_rfl aux2 aux6 le_rfl]
  · ring
  -- now deal with the integrability side goals
  -- (Note we have 5 goals, but the 1st and 3rd are identical. TODO: find a non-hacky way of dealing
  -- with both at once.)
  · rw [intervalIntegrable_iff_integrableOn_Icc_of_le aux6]
    exact (integrablemulsum c ha hb hf_int).mono_set (Set.Icc_subset_Icc_right aux5)
  · rw [intervalIntegrable_iff_integrableOn_Icc_of_le aux5]
    exact (integrablemulsum c ha hb hf_int).mono_set (Set.Icc_subset_Icc_left aux6)
  · rw [intervalIntegrable_iff_integrableOn_Icc_of_le aux6]
    exact (integrablemulsum c ha hb hf_int).mono_set (Set.Icc_subset_Icc_right aux5)
  · rw [intervalIntegrable_iff_integrableOn_Icc_of_le aux3]
    exact (integrablemulsum c ha hb hf_int).mono_set (Set.Icc_subset_Icc_right aux4)
  · exact fun k hk ↦ (intervalIntegrable_iff_integrableOn_Icc_of_le (mod_cast k.le_succ)).mpr
      <| (integrablemulsum c ha hb hf_int).mono_set
        <| (Set.Icc_subset_Icc_iff (mod_cast k.le_succ)).mpr <| mod_cast (ineqofmemIco hk)

end abelSummationProof

theorem sum_mul_eq_sub_integral_mul {b : ℝ} (hb : 0 ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc 0 b, DifferentiableAt ℝ f t)
    (hf_int : IntegrableOn (deriv f) (Set.Icc 0 b)) :
    ∑ k ∈ Icc 0 ⌊b⌋₊, f k * c k =
      f b * (∑ k ∈ Icc 0 ⌊b⌋₊, c k) - ∫ t in Set.Ioc 0 b, deriv f t * (∑ k ∈ Icc 0 ⌊t⌋₊, c k) := by
  nth_rewrite 1 [Finset.Icc_eq_cons_Ioc (Nat.zero_le _)]
  rw [sum_cons, ← Nat.floor_zero (α := ℝ), sum_mul_eq_sub_sub_integral_mul c le_rfl hb hf_diff
    hf_int, Nat.floor_zero, Nat.cast_zero, Icc_self, sum_singleton]
  ring

theorem sum_mul_eq_sub_integral_mul' (hc : c 0 = 0) (b : ℝ)
    (hf_diff : ∀ t ∈ Set.Icc 1 b, DifferentiableAt ℝ f t)
    (hf_int : IntegrableOn (deriv f) (Set.Icc 1 b)) :
    ∑ k ∈ Icc 0 ⌊b⌋₊, f k * c k =
      f b * (∑ k ∈ Icc 0 ⌊b⌋₊, c k) - ∫ t in Set.Ioc 1 b, deriv f t * (∑ k ∈ Icc 0 ⌊t⌋₊, c k) := by
  obtain hb | hb := le_or_gt 1 b
  · have : 1 ≤ ⌊b⌋₊ := (Nat.one_le_floor_iff _).mpr hb
    nth_rewrite 1 [Finset.Icc_eq_cons_Ioc (by linarith), sum_cons, ← Nat.Icc_succ_left,
      Finset.Icc_eq_cons_Ioc (by linarith), sum_cons]
    rw [Nat.succ_eq_add_one, zero_add, ← Nat.floor_one (α := ℝ),
      sum_mul_eq_sub_sub_integral_mul c zero_le_one hb hf_diff hf_int, Nat.floor_one, Nat.cast_one,
      Finset.Icc_eq_cons_Ioc zero_le_one, sum_cons, show 1 = 0 + 1 by rfl, Nat.Ioc_succ_singleton,
      zero_add, sum_singleton, hc, mul_zero, zero_add]
    ring
  · simp_rw [Nat.floor_eq_zero.mpr hb, Icc_self, sum_singleton, Nat.cast_zero, hc, mul_zero,
      Set.Ioc_eq_empty_of_le hb.le, Measure.restrict_empty, integral_zero_measure, sub_self]
