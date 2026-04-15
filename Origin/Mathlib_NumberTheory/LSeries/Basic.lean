/-
Extracted from NumberTheory/LSeries/Basic.lean
Genuine: 23 of 41 | Dissolved: 11 | Infrastructure: 7
-/
import Origin.Core
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.Complex.FiniteDimensional

/-!
# L-series

Given a sequence `f: ℕ → ℂ`, we define the corresponding L-series.

## Main Definitions

 * `LSeries.term f s n` is the `n`th term of the L-series of the sequence `f` at `s : ℂ`.
    We define it to be zero when `n = 0`.

 * `LSeries f` is the L-series with a given sequence `f` as its
    coefficients. This is not the analytic continuation (which does not necessarily exist),
    just the sum of the infinite series if it exists and zero otherwise.

 * `LSeriesSummable f s` indicates that the L-series of `f` converges at `s : ℂ`.

 * `LSeriesHasSum f s a` expresses that the L-series of `f` converges (absolutely)
    at `s : ℂ` to `a : ℂ`.

## Main Results

 * `LSeriesSummable_of_isBigO_rpow`: the `LSeries` of a sequence `f` such that
    `f = O(n^(x-1))` converges at `s` when `x < s.re`.

 * `LSeriesSummable.isBigO_rpow`: if the `LSeries` of `f` is summable at `s`,
    then `f = O(n^(re s))`.

## Notation

We introduce `L` as notation for `LSeries` and `↗f` as notation for `fun n : ℕ ↦ (f n : ℂ)`,
both scoped to `LSeries.notation`. The latter makes it convenient to use arithmetic functions
or Dirichlet characters (or anything that coerces to a function `N → R`, where `ℕ` coerces
to `N` and `R` coerces to `ℂ`) as arguments to `LSeries` etc.

## Tags

L-series
-/

open Complex

/-!
### The terms of an L-series

We define the `n`th term evaluated at a complex number `s` of the L-series associated
to a sequence `f : ℕ → ℂ`, `LSeries.term f s n`, and provide some basic API.

We set `LSeries.term f s 0 = 0`, and for positive `n`, `LSeries.term f s n = f n / n ^ s`.
-/

namespace LSeries

noncomputable

def term (f : ℕ → ℂ) (s : ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else f n / n ^ s

lemma term_def (f : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    term f s n = if n = 0 then 0 else f n / n ^ s :=
  rfl

@[simp]
lemma term_zero (f : ℕ → ℂ) (s : ℂ) : term f s 0 = 0 := rfl

-- DISSOLVED: term_of_ne_zero

-- DISSOLVED: term_of_ne_zero'

-- DISSOLVED: term_congr

lemma norm_term_eq (f : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    ‖term f s n‖ = if n = 0 then 0 else ‖f n‖ / n ^ s.re := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [term_zero, norm_zero, ↓reduceIte]
  · rw [if_neg hn, term_of_ne_zero hn, norm_div, norm_natCast_cpow_of_pos <| Nat.pos_of_ne_zero hn]

lemma norm_term_le {f g : ℕ → ℂ} (s : ℂ) {n : ℕ} (h : ‖f n‖ ≤ ‖g n‖) :
    ‖term f s n‖ ≤ ‖term g s n‖ := by
  simp only [norm_term_eq]
  split
  · rfl
  · gcongr

lemma norm_term_le_of_re_le_re (f : ℕ → ℂ) {s s' : ℂ} (h : s.re ≤ s'.re) (n : ℕ) :
    ‖term f s' n‖ ≤ ‖term f s n‖ := by
  simp only [norm_term_eq]
  split
  next => rfl
  next hn => gcongr; exact Nat.one_le_cast.mpr <| Nat.one_le_iff_ne_zero.mpr hn

section positivity

open scoped ComplexOrder

lemma term_nonneg {a : ℕ → ℂ} {n : ℕ} (h : 0 ≤ a n) (x : ℝ) : 0 ≤ term a x n := by
  rw [term_def]
  split_ifs with hn
  exacts [le_rfl, mul_nonneg h (inv_natCast_cpow_ofReal_pos hn x).le]

-- DISSOLVED: term_pos

end positivity

end LSeries

/-!
### Definition of the L-series and related statements

We define `LSeries f s` of `f : ℕ → ℂ` as the sum over `LSeries.term f s`.
We also provide predicates `LSeriesSummable f s` stating that `LSeries f s` is summable
and `LSeriesHasSum f s a` stating that the L-series of `f` is summable at `s` and converges
to `a : ℂ`.
-/

open LSeries

noncomputable

def LSeries (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑' n, term f s n

-- DISSOLVED: LSeries_congr

def LSeriesSummable (f : ℕ → ℂ) (s : ℂ) : Prop :=
  Summable (term f s)

-- DISSOLVED: LSeriesSummable_congr

open Filter in

lemma LSeriesSummable.congr' {f g : ℕ → ℂ} (s : ℂ) (h : f =ᶠ[atTop] g) (hf : LSeriesSummable f s) :
    LSeriesSummable g s := by
  rw [← Nat.cofinite_eq_atTop] at h
  refine (summable_norm_iff.mpr hf).of_norm_bounded_eventually _ ?_
  have : term f s =ᶠ[cofinite] term g s := by
    rw [eventuallyEq_iff_exists_mem] at h ⊢
    obtain ⟨S, hS, hS'⟩ := h
    refine ⟨S \ {0}, diff_mem hS <| (Set.finite_singleton 0).compl_mem_cofinite, fun n hn ↦ ?_⟩
    simp only [Set.mem_diff, Set.mem_singleton_iff] at hn
    simp only [term_of_ne_zero hn.2, hS' hn.1]
  exact Eventually.mono this.symm fun n hn ↦ by simp only [hn, le_rfl]

open Filter in

lemma LSeriesSummable_congr' {f g : ℕ → ℂ} (s : ℂ) (h : f =ᶠ[atTop] g) :
    LSeriesSummable f s ↔ LSeriesSummable g s :=
  ⟨fun H ↦ H.congr' s h, fun H ↦ H.congr' s h.symm⟩

theorem LSeries.eq_zero_of_not_LSeriesSummable (f : ℕ → ℂ) (s : ℂ) :
    ¬ LSeriesSummable f s → LSeries f s = 0 :=
  tsum_eq_zero_of_not_summable

@[simp]
theorem LSeriesSummable_zero {s : ℂ} : LSeriesSummable 0 s := by
  simp only [LSeriesSummable, funext (term_def 0 s), Pi.zero_apply, zero_div, ite_self,
    summable_zero]

def LSeriesHasSum (f : ℕ → ℂ) (s a : ℂ) : Prop :=
  HasSum (term f s) a

lemma LSeriesHasSum.LSeriesSummable {f : ℕ → ℂ} {s a : ℂ}
    (h : LSeriesHasSum f s a) : LSeriesSummable f s :=
  h.summable

lemma LSeriesHasSum.LSeries_eq {f : ℕ → ℂ} {s a : ℂ}
    (h : LSeriesHasSum f s a) : LSeries f s = a :=
  h.tsum_eq

lemma LSeriesSummable.LSeriesHasSum {f : ℕ → ℂ} {s : ℂ} (h : LSeriesSummable f s) :
    LSeriesHasSum f s (LSeries f s) :=
  h.hasSum

lemma LSeriesHasSum_iff {f : ℕ → ℂ} {s a : ℂ} :
    LSeriesHasSum f s a ↔ LSeriesSummable f s ∧ LSeries f s = a :=
  ⟨fun H ↦ ⟨H.LSeriesSummable, H.LSeries_eq⟩, fun ⟨H₁, H₂⟩ ↦ H₂ ▸ H₁.LSeriesHasSum⟩

-- DISSOLVED: LSeriesHasSum_congr

lemma LSeriesSummable.of_re_le_re {f : ℕ → ℂ} {s s' : ℂ} (h : s.re ≤ s'.re)
    (hf : LSeriesSummable f s) : LSeriesSummable f s' := by
  rw [LSeriesSummable, ← summable_norm_iff] at hf ⊢
  exact hf.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (norm_term_le_of_re_le_re f h)

theorem LSeriesSummable_iff_of_re_eq_re {f : ℕ → ℂ} {s s' : ℂ} (h : s.re = s'.re) :
    LSeriesSummable f s ↔ LSeriesSummable f s' :=
  ⟨fun H ↦ H.of_re_le_re h.le, fun H ↦ H.of_re_le_re h.symm.le⟩

def LSeries.delta (n : ℕ) : ℂ :=
  if n = 1 then 1 else 0

/-!
### Notation
-/

scoped[LSeries.notation] notation "L" => LSeries

scoped[LSeries.notation] notation:max "↗" f:max => fun n : ℕ ↦ (f n : ℂ)

scoped[LSeries.notation] notation "δ" => delta

/-!
### LSeries of 0 and δ
-/

@[simp]
lemma LSeries_zero : LSeries 0 = 0 := by
  ext
  simp only [LSeries, LSeries.term, Pi.zero_apply, zero_div, ite_self, tsum_zero]

section delta

open scoped LSeries.notation

namespace LSeries

open Nat Complex

lemma term_delta (s : ℂ) (n : ℕ) : term δ s n = if n = 1 then 1 else 0 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [term_zero, zero_ne_one, ↓reduceIte]
  · simp only [ne_eq, hn, not_false_eq_true, term_of_ne_zero, delta]
    rcases eq_or_ne n 1 with rfl | hn'
    · simp only [↓reduceIte, cast_one, one_cpow, ne_eq, one_ne_zero, not_false_eq_true, div_self]
    · simp only [hn', ↓reduceIte, zero_div]

lemma mul_delta_eq_smul_delta {f : ℕ → ℂ} : f * δ = f 1 • δ := by
  ext n
  simp only [Pi.mul_apply, delta, mul_ite, mul_one, mul_zero, Pi.smul_apply, smul_eq_mul]
  split_ifs with hn <;> simp only [hn]

lemma mul_delta {f : ℕ → ℂ} (h : f 1 = 1) : f * δ = δ := by
  rw [mul_delta_eq_smul_delta, h, one_smul]

lemma delta_mul_eq_smul_delta {f : ℕ → ℂ} : δ * f = f 1 • δ :=
  mul_comm δ f ▸ mul_delta_eq_smul_delta

lemma delta_mul {f : ℕ → ℂ} (h : f 1 = 1) : δ * f = δ :=
  mul_comm δ f ▸ mul_delta h

end LSeries

lemma LSeries_delta : LSeries δ = 1 := by
  ext
  simp only [LSeries, LSeries.term_delta, tsum_ite_eq, Pi.one_apply]

end delta

/-!
### Criteria for and consequences of summability of L-series

We relate summability of L-series with bounds on the coefficients in terms of powers of `n`.
-/

-- DISSOLVED: LSeriesSummable.le_const_mul_rpow

open Filter in

lemma LSeriesSummable.isBigO_rpow {f : ℕ → ℂ} {s : ℂ} (h : LSeriesSummable f s) :
    f =O[atTop] fun n ↦ (n : ℝ) ^ s.re := by
  obtain ⟨C, hC⟩ := h.le_const_mul_rpow
  refine Asymptotics.IsBigO.of_bound C <| eventually_atTop.mpr ⟨1, fun n hn ↦ ?_⟩
  convert hC n (Nat.pos_iff_ne_zero.mp hn) using 2
  rw [Real.norm_eq_abs, Real.abs_rpow_of_nonneg n.cast_nonneg, _root_.abs_of_nonneg n.cast_nonneg]

-- DISSOLVED: LSeriesSummable_of_le_const_mul_rpow

open Filter Finset Real Nat in

lemma LSeriesSummable_of_isBigO_rpow {f : ℕ → ℂ} {x : ℝ} {s : ℂ} (hs : x < s.re)
    (h : f =O[atTop] fun n ↦ (n : ℝ) ^ (x - 1)) :
    LSeriesSummable f s := by
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp h
  obtain ⟨m, hm⟩ := eventually_atTop.mp hC
  let C' := max C (max' (insert 0 (image (fun n : ℕ ↦ ‖f n‖ / (n : ℝ) ^ (x - 1)) (range m)))
    (insert_nonempty 0 _))
  have hC'₀ : 0 ≤ C' := (le_max' _ _ (mem_insert.mpr (Or.inl rfl))).trans <| le_max_right ..
  have hCC' : C ≤ C' := le_max_left ..
  refine LSeriesSummable_of_le_const_mul_rpow hs ⟨C', fun n hn₀ ↦ ?_⟩
  rcases le_or_lt m n with hn | hn
  · refine (hm n hn).trans ?_
    have hn₀ : (0 : ℝ) ≤ n := cast_nonneg _
    gcongr
    rw [Real.norm_eq_abs, abs_rpow_of_nonneg hn₀, _root_.abs_of_nonneg hn₀]
  · have hn' : 0 < n := Nat.pos_of_ne_zero hn₀
    refine (div_le_iff₀ <| rpow_pos_of_pos (cast_pos.mpr hn') _).mp ?_
    refine (le_max' _ _ <| mem_insert_of_mem ?_).trans <| le_max_right ..
    exact mem_image.mpr ⟨n, mem_range.mpr hn, rfl⟩

-- DISSOLVED: LSeriesSummable_of_bounded_of_one_lt_re

-- DISSOLVED: LSeriesSummable_of_bounded_of_one_lt_real
