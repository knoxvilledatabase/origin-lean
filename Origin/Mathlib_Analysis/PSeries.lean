/-
Extracted from Analysis/PSeries.lean
Genuine: 16 of 18 | Dissolved: 2 | Infrastructure: 0
-/
import Origin.Core

/-!
# Convergence of `p`-series

In this file we prove that the series `∑' k in ℕ, 1 / k ^ p` converges if and only if `p > 1`.
The proof is based on the
[Cauchy condensation test](https://en.wikipedia.org/wiki/Cauchy_condensation_test): `∑ k, f k`
converges if and only if so does `∑ k, 2 ^ k f (2 ^ k)`. We prove this test in
`NNReal.summable_condensed_iff` and `summable_condensed_iff_of_nonneg`, then use it to prove
`summable_one_div_rpow`. After this transformation, a `p`-series turns into a geometric series.

## Tags

p-series, Cauchy condensation test
-/

/-!
### Schlömilch's generalization of the Cauchy condensation test

In this section we prove the Schlömilch's generalization of the Cauchy condensation test:
for a strictly increasing `u : ℕ → ℕ` with ratio of successive differences bounded and an
antitone `f : ℕ → ℝ≥0` or `f : ℕ → ℝ`, `∑ k, f k` converges if and only if
so does `∑ k, (u (k + 1) - u k) * f (u k)`. Instead of giving a monolithic proof, we split it
into a series of lemmas with explicit estimates of partial sums of each series in terms of the
partial sums of the other series.
-/

def SuccDiffBounded (C : ℕ) (u : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, u (n + 2) - u (n + 1) ≤ C • (u (n + 1) - u n)

namespace Finset

variable {M : Type*} [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]
  {f : ℕ → M} {u : ℕ → ℕ}

theorem le_sum_schlomilch' (hf : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) (h_pos : ∀ n, 0 < u n)
    (hu : Monotone u) (n : ℕ) :
    (∑ k ∈ Ico (u 0) (u n), f k) ≤ ∑ k ∈ range n, (u (k + 1) - u k) • f (u k) := by
  induction n with
  | zero => simp
  | succ n ihn =>
    suffices (∑ k ∈ Ico (u n) (u (n + 1)), f k) ≤ (u (n + 1) - u n) • f (u n) by
      rw [sum_range_succ, ← sum_Ico_consecutive]
      · exact add_le_add ihn this
      exacts [hu n.zero_le, hu n.le_succ]
    have : ∀ k ∈ Ico (u n) (u (n + 1)), f k ≤ f (u n) := fun k hk =>
      hf (Nat.succ_le_of_lt (h_pos n)) (mem_Ico.mp hk).1
    convert sum_le_sum this
    simp

theorem le_sum_condensed' (hf : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) (n : ℕ) :
    (∑ k ∈ Ico 1 (2 ^ n), f k) ≤ ∑ k ∈ range n, 2 ^ k • f (2 ^ k) := by
  convert le_sum_schlomilch' hf (fun n => pow_pos zero_lt_two n)
    (fun m n hm => pow_right_mono₀ one_le_two hm) n using 2
  simp [pow_succ, mul_two]

theorem le_sum_schlomilch (hf : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) (h_pos : ∀ n, 0 < u n)
    (hu : Monotone u) (n : ℕ) :
    (∑ k ∈ range (u n), f k) ≤
      ∑ k ∈ range (u 0), f k + ∑ k ∈ range n, (u (k + 1) - u k) • f (u k) := by
  grw [← le_sum_schlomilch' hf h_pos hu n, ← sum_range_add_sum_Ico _ (hu n.zero_le)]

theorem le_sum_condensed (hf : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) (n : ℕ) :
    (∑ k ∈ range (2 ^ n), f k) ≤ f 0 + ∑ k ∈ range n, 2 ^ k • f (2 ^ k) := by
  grw [← le_sum_condensed' hf n, ← sum_range_add_sum_Ico _ n.one_le_two_pow, sum_range_succ,
    sum_range_zero, zero_add]

theorem sum_schlomilch_le' (hf : ∀ ⦃m n⦄, 1 < m → m ≤ n → f n ≤ f m) (h_pos : ∀ n, 0 < u n)
    (hu : Monotone u) (n : ℕ) :
    (∑ k ∈ range n, (u (k + 1) - u k) • f (u (k + 1))) ≤ ∑ k ∈ Ico (u 0 + 1) (u n + 1), f k := by
  induction n with
  | zero => simp
  | succ n ihn =>
    suffices (u (n + 1) - u n) • f (u (n + 1)) ≤ ∑ k ∈ Ico (u n + 1) (u (n + 1) + 1), f k by
      rw [sum_range_succ, ← sum_Ico_consecutive]
      exacts [add_le_add ihn this,
        (add_le_add_left (hu n.zero_le) _ : u 0 + 1 ≤ u n + 1),
        add_le_add_left (hu n.le_succ) _]
    have : ∀ k ∈ Ico (u n + 1) (u (n + 1) + 1), f (u (n + 1)) ≤ f k := fun k hk =>
      hf (Nat.lt_of_le_of_lt (Nat.succ_le_of_lt (h_pos n)) <| (Nat.lt_succ_of_le le_rfl).trans_le
        (mem_Ico.mp hk).1) (Nat.le_of_lt_succ <| (mem_Ico.mp hk).2)
    convert sum_le_sum this
    simp

theorem sum_condensed_le' (hf : ∀ ⦃m n⦄, 1 < m → m ≤ n → f n ≤ f m) (n : ℕ) :
    (∑ k ∈ range n, 2 ^ k • f (2 ^ (k + 1))) ≤ ∑ k ∈ Ico 2 (2 ^ n + 1), f k := by
  convert sum_schlomilch_le' hf (fun n => pow_pos zero_lt_two n)
    (fun m n hm => pow_right_mono₀ one_le_two hm) n using 2
  simp [pow_succ, mul_two]

theorem sum_schlomilch_le {C : ℕ} (hf : ∀ ⦃m n⦄, 1 < m → m ≤ n → f n ≤ f m) (h_pos : ∀ n, 0 < u n)
    (h_nonneg : ∀ n, 0 ≤ f n) (hu : Monotone u) (h_succ_diff : SuccDiffBounded C u) (n : ℕ) :
    ∑ k ∈ range (n + 1), (u (k + 1) - u k) • f (u k) ≤
    (u 1 - u 0) • f (u 0) + C • ∑ k ∈ Ico (u 0 + 1) (u n + 1), f k := by
  rw [sum_range_succ', add_comm]
  gcongr
  suffices ∑ k ∈ range n, (u (k + 2) - u (k + 1)) • f (u (k + 1)) ≤
  C • ∑ k ∈ range n, ((u (k + 1) - u k) • f (u (k + 1))) by
    refine this.trans (nsmul_le_nsmul_right ?_ _)
    exact sum_schlomilch_le' hf h_pos hu n
  have : ∀ k ∈ range n, (u (k + 2) - u (k + 1)) • f (u (k + 1)) ≤
    C • ((u (k + 1) - u k) • f (u (k + 1))) := by
    intro k _
    rw [smul_smul]
    gcongr
    · exact h_nonneg (u (k + 1))
    exact mod_cast h_succ_diff k
  convert sum_le_sum this
  simp [smul_sum]

theorem sum_condensed_le (hf : ∀ ⦃m n⦄, 1 < m → m ≤ n → f n ≤ f m) (n : ℕ) :
    (∑ k ∈ range (n + 1), 2 ^ k • f (2 ^ k)) ≤ f 1 + 2 • ∑ k ∈ Ico 2 (2 ^ n + 1), f k := by
  grw [← sum_condensed_le' hf n]
  simp [sum_range_succ', add_comm, pow_succ', mul_nsmul', sum_nsmul]

end Finset

namespace ENNReal

open Filter Finset

variable {u : ℕ → ℕ} {f : ℕ → ℝ≥0∞}

open NNReal in

theorem le_tsum_schlomilch (hf : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) (h_pos : ∀ n, 0 < u n)
    (hu : StrictMono u) :
    ∑' k, f k ≤ ∑ k ∈ range (u 0), f k + ∑' k : ℕ, (u (k + 1) - u k) * f (u k) := by
  rw [ENNReal.tsum_eq_iSup_nat' hu.tendsto_atTop]
  refine iSup_le fun n => ?_
  grw [Finset.le_sum_schlomilch hf h_pos hu.monotone n]
  gcongr
  have (k : ℕ) : (u (k + 1) - u k : ℝ≥0∞) = (u (k + 1) - (u k : ℕ) : ℕ) := by simp
  simp only [nsmul_eq_mul, this]
  apply ENNReal.sum_le_tsum

theorem le_tsum_condensed (hf : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) :
    ∑' k, f k ≤ f 0 + ∑' k : ℕ, 2 ^ k * f (2 ^ k) := by
  rw [ENNReal.tsum_eq_iSup_nat' (tendsto_pow_atTop_atTop_of_one_lt _root_.one_lt_two)]
  refine iSup_le fun n => (Finset.le_sum_condensed hf n).trans ?_
  simp only [nsmul_eq_mul, Nat.cast_pow, Nat.cast_two]
  grw [ENNReal.sum_le_tsum]

theorem tsum_schlomilch_le {C : ℕ} (hf : ∀ ⦃m n⦄, 1 < m → m ≤ n → f n ≤ f m) (h_pos : ∀ n, 0 < u n)
    (h_nonneg : ∀ n, 0 ≤ f n) (hu : Monotone u) (h_succ_diff : SuccDiffBounded C u) :
    ∑' k : ℕ, (u (k + 1) - u k) * f (u k) ≤ (u 1 - u 0) * f (u 0) + C * ∑' k, f k := by
  rw [ENNReal.tsum_eq_iSup_nat' (tendsto_atTop_mono Nat.le_succ tendsto_id)]
  refine iSup_le fun n => ?_
  grw [← ENNReal.sum_le_tsum <| Finset.Ico (u 0 + 1) (u n + 1)]
  simpa using Finset.sum_schlomilch_le hf h_pos h_nonneg hu h_succ_diff n

theorem tsum_condensed_le (hf : ∀ ⦃m n⦄, 1 < m → m ≤ n → f n ≤ f m) :
    (∑' k : ℕ, 2 ^ k * f (2 ^ k)) ≤ f 1 + 2 * ∑' k, f k := by
  rw [ENNReal.tsum_eq_iSup_nat' (tendsto_atTop_mono Nat.le_succ tendsto_id), two_mul, ← two_nsmul]
  refine iSup_le fun n => ?_
  grw [← ENNReal.sum_le_tsum <| Finset.Ico 2 (2 ^ n + 1)]
  simpa using Finset.sum_condensed_le hf n

end ENNReal

namespace NNReal

open Finset

open ENNReal in

-- DISSOLVED: summable_schlomilch_iff

open ENNReal in

theorem summable_condensed_iff {f : ℕ → ℝ≥0} (hf : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) :
    (Summable fun k : ℕ => (2 : ℝ≥0) ^ k * f (2 ^ k)) ↔ Summable f := by
  have h_succ_diff : SuccDiffBounded 2 (2 ^ ·) := by
    intro n
    simp [pow_succ, mul_two, two_mul]
  convert summable_schlomilch_iff hf (pow_pos zero_lt_two) (pow_right_strictMono₀ _root_.one_lt_two)
    two_ne_zero h_succ_diff
  simp [pow_succ, mul_two]

end NNReal

open NNReal in

-- DISSOLVED: summable_schlomilch_iff_of_nonneg

theorem summable_condensed_iff_of_nonneg {f : ℕ → ℝ} (h_nonneg : ∀ n, 0 ≤ f n)
    (h_mono : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) :
    (Summable fun k : ℕ => (2 : ℝ) ^ k * f (2 ^ k)) ↔ Summable f := by
  have h_succ_diff : SuccDiffBounded 2 (2 ^ ·) := by
    intro n
    simp [pow_succ, mul_two, two_mul]
  convert summable_schlomilch_iff_of_nonneg h_nonneg h_mono (pow_pos zero_lt_two)
    (pow_right_strictMono₀ one_lt_two) two_ne_zero h_succ_diff
  simp [pow_succ, mul_two]

theorem summable_condensed_iff_of_eventually_nonneg {f : ℕ → ℝ} (h_nonneg : 0 ≤ᶠ[Filter.atTop] f)
    (h_mono : ∀ᶠ k in Filter.atTop, f (k + 1) ≤ f k) :
    (Summable fun k : ℕ => (2 : ℝ) ^ k * f (2 ^ k)) ↔ Summable f := by
  rw [Filter.EventuallyLE, Filter.eventually_atTop] at h_nonneg
  rw [Filter.eventually_atTop] at h_mono
  rcases h_nonneg with ⟨n, hn⟩
  rcases h_mono with ⟨m, hm⟩
  convert summable_condensed_iff_of_nonneg (f := fun k ↦ f (max k (n + m))) _ _ using 1
  · rw [summable_congr_atTop]
    have h_pow := tendsto_pow_atTop_atTop_of_one_lt (r := 2) (by simp)
    filter_upwards [h_pow.eventually_ge_atTop (n + m)] with _ hk using by simp [max_eq_left hk]
  · rw [summable_congr_atTop]
    filter_upwards [Filter.eventually_ge_atTop (n + m)] with _ hk using by simp [max_eq_left hk]
  · simp_all
  · intro _ _ _ _
    exact antitoneOn_nat_Ici_of_succ_le (k := n + m) (by grind) (by simp) (by simp) (by grind)

section p_series

/-!
### Convergence of the `p`-series

In this section we prove that for a real number `p`, the series `∑' n : ℕ, 1 / (n ^ p)` converges if
and only if `1 < p`. There are many different proofs of this fact. The proof in this file uses the
Cauchy condensation test we formalized above. This test implies that `∑ n, 1 / (n ^ p)` converges if
and only if `∑ n, 2 ^ n / ((2 ^ n) ^ p)` converges, and the latter series is a geometric series with
common ratio `2 ^ {1 - p}`. -/

namespace Real

open Filter
