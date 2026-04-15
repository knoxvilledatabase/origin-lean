/-
Extracted from NumberTheory/LegendreSymbol/GaussEisensteinLemmas.lean
Genuine: 2 of 10 | Dissolved: 8 | Infrastructure: 0
-/
import Origin.Core

/-!
# Lemmas of Gauss and Eisenstein

This file contains the Lemmas of Gauss and Eisenstein on the Legendre symbol.
The main results are `ZMod.gauss_lemma` and `ZMod.eisenstein_lemma`.
-/

open Finset Nat

open scoped Nat

section GaussEisenstein

namespace ZMod

-- DISSOLVED: Ico_map_valMinAbs_natAbs_eq_Ico_map_id

-- DISSOLVED: gauss_lemma_aux₁

-- DISSOLVED: gauss_lemma_aux

-- DISSOLVED: gauss_lemma

-- DISSOLVED: eisenstein_lemma_aux₁

-- DISSOLVED: eisenstein_lemma_aux

theorem div_eq_filter_card {a b c : ℕ} (hb0 : 0 < b) (hc : a / b ≤ c) :
    a / b = #{x ∈ Ico 1 c.succ | x * b ≤ a} :=
  calc
    a / b = #(Ico 1 (a / b).succ) := by simp
    _ = #{x ∈ Ico 1 c.succ | x * b ≤ a} :=
      congr_arg _ <| Finset.ext fun x => by
        have : x * b ≤ a → x ≤ c := fun h => le_trans (by rwa [le_div_iff_mul_le hb0]) hc
        simp [le_div_iff_mul_le hb0]; tauto

private theorem sum_Ico_eq_card_lt {p q : ℕ} :
    ∑ a ∈ Ico 1 (p / 2).succ, a * q / p =
      #{x ∈ Ico 1 (p / 2).succ ×ˢ Ico 1 (q / 2).succ | x.2 * p ≤ x.1 * q} :=
  if hp0 : p = 0 then by simp [hp0]
  else
    calc
      ∑ a ∈ Ico 1 (p / 2).succ, a * q / p =
          ∑ a ∈ Ico 1 (p / 2).succ, #{x ∈ Ico 1 (q / 2).succ | x * p ≤ a * q} :=
        Finset.sum_congr rfl fun x hx => div_eq_filter_card (Nat.pos_of_ne_zero hp0) <|
          calc
            x * q / p ≤ p / 2 * q / p := by have := le_of_lt_succ (mem_Ico.mp hx).2; gcongr
            _ ≤ _ := Nat.div_mul_div_le_div _ _ _
      _ = _ := by simp only [card_eq_sum_ones, sum_filter, sum_product]

-- DISSOLVED: sum_mul_div_add_sum_mul_div_eq_mul

-- DISSOLVED: eisenstein_lemma

end ZMod

end GaussEisenstein
