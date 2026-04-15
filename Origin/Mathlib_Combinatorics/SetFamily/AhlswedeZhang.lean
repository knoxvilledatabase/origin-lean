/-
Extracted from Combinatorics/SetFamily/AhlswedeZhang.lean
Genuine: 7 of 7 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The Ahlswede-Zhang identity

This file proves the Ahlswede-Zhang identity, which is a nontrivial relation between the size of the
"truncated unions" of a set family. It sharpens the Lubell-Yamamoto-Meshalkin inequality
`Finset.lubell_yamamoto_meshalkin_inequality_sum_card_div_choose`, by making explicit the correction
term.

For a set family `𝒜` over a ground set of size `n`, the Ahlswede-Zhang identity states that the sum
of `|⋂ B ∈ 𝒜, B ⊆ A, B|/(|A| * n.choose |A|)` over all sets `A` is exactly `1`. This implies the LYM
inequality since for an antichain `𝒜` and every `A ∈ 𝒜` we have
`|⋂ B ∈ 𝒜, B ⊆ A, B|/(|A| * n.choose |A|) = 1 / n.choose |A|`.

## Main declarations

* `Finset.truncatedSup`: `s.truncatedSup a` is the supremum of all `b ≥ a` in `𝒜` if there are
  some, or `⊤` if there are none.
* `Finset.truncatedInf`: `s.truncatedInf a` is the infimum of all `b ≤ a` in `𝒜` if there are
  some, or `⊥` if there are none.
* `AhlswedeZhang.infSum`: LHS of the Ahlswede-Zhang identity.
* `AhlswedeZhang.le_infSum`: The sum of `1 / n.choose |A|` over an antichain is less than the RHS of
  the Ahlswede-Zhang identity.
* `AhlswedeZhang.infSum_eq_one`: Ahlswede-Zhang identity.

## References

* [R. Ahlswede, Z. Zhang, *An identity in combinatorial extremal theory*](https://doi.org/10.1016/0001-8708(90)90023-G)
* [D. T. Tru, *An AZ-style identity and Bollobás deficiency*](https://doi.org/10.1016/j.jcta.2007.03.005)
-/

variable (α : Type*) [Fintype α] [Nonempty α] {m n : ℕ}

open Finset Fintype Nat

private lemma binomial_sum_eq (h : n < m) :
    ∑ i ∈ range (n + 1), (n.choose i * (m - n) / ((m - i) * m.choose i) : ℚ) = 1 := by
  set f : ℕ → ℚ := fun i ↦ n.choose i * (m.choose i : ℚ)⁻¹ with hf
  suffices ∀ i ∈ range (n + 1), f i - f (i + 1) = n.choose i * (m - n) / ((m - i) * m.choose i) by
    rw [← sum_congr rfl this, sum_range_sub', hf]
    simp [choose_zero_right]
  intro i h₁
  rw [mem_range] at h₁
  have h₁ := le_of_lt_succ h₁
  have h₂ := h₁.trans_lt h
  have h₃ := h₂.le
  have hi₄ : (i + 1 : ℚ) ≠ 0 := i.cast_add_one_ne_zero
  have := congr_arg ((↑) : ℕ → ℚ) (choose_succ_right_eq m i)
  push_cast at this
  dsimp [f, hf]
  rw [(eq_mul_inv_iff_mul_eq₀ hi₄).mpr this]
  have := congr_arg ((↑) : ℕ → ℚ) (choose_succ_right_eq n i)
  push_cast at this
  rw [(eq_mul_inv_iff_mul_eq₀ hi₄).mpr this]
  have : (m - i : ℚ) ≠ 0 := sub_ne_zero_of_ne (cast_lt.mpr h₂).ne'
  have : (m.choose i : ℚ) ≠ 0 := cast_ne_zero.2 (choose_pos h₂.le).ne'
  simp [field, *]

private lemma Fintype.sum_div_mul_card_choose_card :
    ∑ s : Finset α, (card α / ((card α - #s) * (card α).choose #s) : ℚ) =
      card α * ∑ k ∈ range (card α), (↑k)⁻¹ + 1 := by
  rw [← powerset_univ, powerset_card_disjiUnion, sum_disjiUnion]
  have : ∀ {x : ℕ}, ∀ s ∈ powersetCard x (univ : Finset α),
    (card α / ((card α - #s) * (card α).choose #s) : ℚ) =
      card α / ((card α - x) * (card α).choose x) := by
    intro n s hs
    rw [mem_powersetCard_univ.1 hs]
  simp_rw [Finset.sum_congr rfl this, sum_const, card_powersetCard, card_univ, nsmul_eq_mul,
    mul_div, mul_comm, ← mul_div]
  rw [← mul_sum, ← mul_inv_cancel₀ (cast_ne_zero.mpr card_ne_zero : (card α : ℚ) ≠ 0), ← mul_add,
    add_comm _ ((card α)⁻¹ : ℚ), ← sum_insert (f := fun x : ℕ ↦ (x⁻¹ : ℚ)) notMem_range_self,
    ← range_add_one]
  have (n) (hn : n ∈ range (card α + 1)) :
      ((card α).choose n / ((card α - n) * (card α).choose n) : ℚ) = (card α - n : ℚ)⁻¹ := by
    rw [div_mul_cancel_right₀]
    exact cast_ne_zero.2 (choose_pos <| mem_range_succ_iff.1 hn).ne'
  simp only [Finset.sum_congr rfl this, mul_eq_mul_left_iff, cast_eq_zero]
  convert Or.inl <| sum_range_reflect _ _ with a ha
  rw [add_tsub_cancel_right, cast_sub (mem_range_succ_iff.mp ha)]

end

open scoped FinsetFamily

namespace Finset

variable {α β : Type*}

/-! ### Truncated supremum, truncated infimum -/

section SemilatticeSup

variable [SemilatticeSup α] [SemilatticeSup β] [BoundedOrder β] {s t : Finset α} {a : α}

set_option backward.privateInPublic true in

private lemma sup_aux [DecidableLE α] : a ∈ lowerClosure s → {b ∈ s | a ≤ b}.Nonempty :=
  fun ⟨b, hb, hab⟩ ↦ ⟨b, mem_filter.2 ⟨hb, hab⟩⟩

private lemma lower_aux [DecidableEq α] :
    a ∈ lowerClosure ↑(s ∪ t) ↔ a ∈ lowerClosure s ∨ a ∈ lowerClosure t := by
  rw [coe_union, lowerClosure_union, LowerSet.mem_sup_iff]

variable [DecidableLE α] [OrderTop α]

set_option backward.privateInPublic true in

set_option backward.privateInPublic.warn false in

def truncatedSup (s : Finset α) (a : α) : α :=
  if h : a ∈ lowerClosure s then {b ∈ s | a ≤ b}.sup' (sup_aux h) id else ⊤

set_option backward.privateInPublic true in

set_option backward.privateInPublic.warn false in

lemma truncatedSup_of_mem (h : a ∈ lowerClosure s) :
    truncatedSup s a = {b ∈ s | a ≤ b}.sup' (sup_aux h) id := dif_pos h

lemma truncatedSup_of_notMem (h : a ∉ lowerClosure s) : truncatedSup s a = ⊤ := dif_neg h
