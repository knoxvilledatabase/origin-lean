/-
Extracted from Algebra/Order/CauSeq/BigOperators.lean
Genuine: 6 | Conflates: 1 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core
import Mathlib.Algebra.GeomSum
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.CauSeq.Basic

noncomputable section

/-!
# Cauchy sequences and big operators

This file proves some more lemmas about basic Cauchy sequences that involve finite sums.
-/

open Finset IsAbsoluteValue

namespace IsCauSeq

variable {α β : Type*} [LinearOrderedField α] [Ring β] {abv : β → α} [IsAbsoluteValue abv]
  {f g : ℕ → β} {a : ℕ → α}

lemma of_abv_le (n : ℕ) (hm : ∀ m, n ≤ m → abv (f m) ≤ a m) :
    IsCauSeq abs (fun n ↦ ∑ i ∈ range n, a i) → IsCauSeq abv fun n ↦ ∑ i ∈ range n, f i := by
  intro hg ε ε0
  cases' hg (ε / 2) (div_pos ε0 (by norm_num)) with i hi
  exists max n i
  intro j ji
  have hi₁ := hi j (le_trans (le_max_right n i) ji)
  have hi₂ := hi (max n i) (le_max_right n i)
  have sub_le :=
    abs_sub_le (∑ k ∈ range j, a k) (∑ k ∈ range i, a k) (∑ k ∈ range (max n i), a k)
  have := add_lt_add hi₁ hi₂
  rw [abs_sub_comm (∑ k ∈ range (max n i), a k), add_halves ε] at this
  refine lt_of_le_of_lt (le_trans (le_trans ?_ (le_abs_self _)) sub_le) this
  generalize hk : j - max n i = k
  clear this hi₂ hi₁ hi ε0 ε hg sub_le
  rw [tsub_eq_iff_eq_add_of_le ji] at hk
  rw [hk]
  dsimp only
  clear hk ji j
  induction' k with k' hi
  · simp [abv_zero abv]
  simp only [Nat.succ_add, Nat.succ_eq_add_one, Finset.sum_range_succ_comm]
  simp only [add_assoc, sub_eq_add_neg]
  refine le_trans (abv_add _ _ _) ?_
  simp only [sub_eq_add_neg] at hi
  exact add_le_add (hm _ (le_add_of_nonneg_of_le (Nat.zero_le _) (le_max_left _ _))) hi

lemma of_abv (hf : IsCauSeq abs fun m ↦ ∑ n ∈ range m, abv (f n)) :
    IsCauSeq abv fun m ↦ ∑ n ∈ range m, f n :=
  hf.of_abv_le 0 fun _ _ ↦ le_rfl

variable [Archimedean α]

lemma of_decreasing_bounded (f : ℕ → α) {a : α} {m : ℕ} (ham : ∀ n ≥ m, |f n| ≤ a)
    (hnm : ∀ n ≥ m, f n.succ ≤ f n) : IsCauSeq abs f := fun ε ε0 ↦ by
  classical
  let ⟨k, hk⟩ := Archimedean.arch a ε0
  have h : ∃ l, ∀ n ≥ m, a - l • ε < f n :=
    ⟨k + k + 1, fun n hnm ↦
      lt_of_lt_of_le (show a - (k + (k + 1)) • ε < -|f n| from
          lt_neg.1 <| (ham n hnm).trans_lt
              (by
                rw [neg_sub, lt_sub_iff_add_lt, add_nsmul, add_nsmul, one_nsmul]
                exact add_lt_add_of_le_of_lt hk (lt_of_le_of_lt hk (lt_add_of_pos_right _ ε0))))
        (neg_le.2 <| abs_neg (f n) ▸ le_abs_self _)⟩
  let l := Nat.find h
  have hl : ∀ n : ℕ, n ≥ m → f n > a - l • ε := Nat.find_spec h
  have hl0 : l ≠ 0 := fun hl0 ↦
    not_lt_of_ge (ham m le_rfl)
      (lt_of_lt_of_le (by have := hl m (le_refl m); simpa [hl0] using this) (le_abs_self (f m)))
  cases' not_forall.1 (Nat.find_min h (Nat.pred_lt hl0)) with i hi
  rw [Classical.not_imp, not_lt] at hi
  exists i
  intro j hj
  have hfij : f j ≤ f i := (Nat.rel_of_forall_rel_succ_of_le_of_le (· ≥ ·) hnm hi.1 hj).le
  rw [abs_of_nonpos (sub_nonpos.2 hfij), neg_sub, sub_lt_iff_lt_add']
  calc
    f i ≤ a - Nat.pred l • ε := hi.2
    _ = a - l • ε + ε := by
      conv =>
        rhs
        rw [← Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hl0), succ_nsmul, sub_add,
          add_sub_cancel_right]
    _ < f j + ε := add_lt_add_right (hl j (le_trans hi.1 hj)) _

lemma of_mono_bounded (f : ℕ → α) {a : α} {m : ℕ} (ham : ∀ n ≥ m, |f n| ≤ a)
    (hnm : ∀ n ≥ m, f n ≤ f n.succ) : IsCauSeq abs f :=
  (of_decreasing_bounded (-f) (a := a) (m := m) (by simpa using ham) <| by simpa using hnm).of_neg

-- CONFLATES (assumes ground = zero): geo_series
lemma geo_series [Nontrivial β] (x : β) (hx1 : abv x < 1) :
    IsCauSeq abv fun n ↦ ∑ m ∈ range n, x ^ m := by
  have hx1' : abv x ≠ 1 := fun h ↦ by simp [h, lt_irrefl] at hx1
  refine of_abv ?_
  simp only [abv_pow abv, geom_sum_eq hx1']
  conv in _ / _ => rw [← neg_div_neg_eq, neg_sub, neg_sub]
  have : 0 < 1 - abv x := sub_pos.2 hx1
  refine @of_mono_bounded _ _ _ _ ((1 : α) / (1 - abv x)) 0 ?_ ?_
  · intro n _
    rw [abs_of_nonneg]
    · gcongr
      exact sub_le_self _ (abv_pow abv x n ▸ abv_nonneg _ _)
    refine div_nonneg (sub_nonneg.2 ?_) (sub_nonneg.2 <| le_of_lt hx1)
    exact pow_le_one₀ (by positivity) hx1.le
  · intro n _
    rw [← one_mul (abv x ^ n), pow_succ']
    gcongr

lemma geo_series_const (a : α) {x : α} (hx1 : |x| < 1) :
    IsCauSeq abs fun m ↦ ∑ n ∈ range m, (a * x ^ n) := by
  simpa [mul_sum, Pi.mul_def] using (const a).mul (geo_series x hx1)

lemma series_ratio_test {f : ℕ → β} (n : ℕ) (r : α) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (h : ∀ m, n ≤ m → abv (f m.succ) ≤ r * abv (f m)) :
    IsCauSeq abv fun m ↦ ∑ n ∈ range m, f n := by
  have har1 : |r| < 1 := by rwa [abs_of_nonneg hr0]
  refine (geo_series_const (abv (f n.succ) * r⁻¹ ^ n.succ) har1).of_abv_le n.succ fun m hmn ↦ ?_
  obtain rfl | hr := hr0.eq_or_lt
  · have m_pos := lt_of_lt_of_le (Nat.succ_pos n) hmn
    have := h m.pred (Nat.le_of_succ_le_succ (by rwa [Nat.succ_pred_eq_of_pos m_pos]))
    simpa [Nat.sub_add_cancel m_pos, pow_succ] using this
  generalize hk : m - n.succ = k
  replace hk : m = k + n.succ := (tsub_eq_iff_eq_add_of_le hmn).1 hk
  induction' k with k ih generalizing m n
  · rw [hk, Nat.zero_add, mul_right_comm, inv_pow _ _, ← div_eq_mul_inv, mul_div_cancel_right₀]
    positivity
  · have kn : k + n.succ ≥ n.succ := by
      rw [← zero_add n.succ]; exact add_le_add (Nat.zero_le _) (by simp)
    rw [hk, Nat.succ_add, pow_succ r, ← mul_assoc]
    refine
      le_trans (by rw [mul_comm] <;> exact h _ (Nat.le_of_succ_le kn))
        (mul_le_mul_of_nonneg_right ?_ hr0)
    exact ih _ h _ (by simp) rfl

end IsCauSeq
