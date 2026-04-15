/-
Extracted from Combinatorics/SetFamily/LYM.lean
Genuine: 11 of 12 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SetFamily.Shadow

/-!
# Lubell-Yamamoto-Meshalkin inequality and Sperner's theorem

This file proves the local LYM and LYM inequalities as well as Sperner's theorem.

## Main declarations

* `Finset.card_div_choose_le_card_shadow_div_choose`: Local Lubell-Yamamoto-Meshalkin inequality.
  The shadow of a set `𝒜` in a layer takes a greater proportion of its layer than `𝒜` does.
* `Finset.sum_card_slice_div_choose_le_one`: Lubell-Yamamoto-Meshalkin inequality. The sum of
  densities of `𝒜` in each layer is at most `1` for any antichain `𝒜`.
* `IsAntichain.sperner`: Sperner's theorem. The size of any antichain in `Finset α` is at most the
  size of the maximal layer of `Finset α`. It is a corollary of `sum_card_slice_div_choose_le_one`.

## TODO

Prove upward local LYM.

Provide equality cases. Local LYM gives that the equality case of LYM and Sperner is precisely when
`𝒜` is a middle layer.

`falling` could be useful more generally in grade orders.

## References

* http://b-mehta.github.io/maths-notes/iii/mich/combinatorics.pdf
* http://discretemath.imp.fu-berlin.de/DMII-2015-16/kruskal.pdf

## Tags

shadow, lym, slice, sperner, antichain
-/

open Finset Nat

open FinsetFamily

variable {𝕜 α : Type*} [LinearOrderedField 𝕜]

namespace Finset

/-! ### Local LYM inequality -/

section LocalLYM

variable [DecidableEq α] [Fintype α]
  {𝒜 : Finset (Finset α)} {r : ℕ}

theorem card_mul_le_card_shadow_mul (h𝒜 : (𝒜 : Set (Finset α)).Sized r) :
    #𝒜 * r ≤ #(∂ 𝒜) * (Fintype.card α - r + 1) := by
  let i : DecidableRel ((· ⊆ ·) : Finset α → Finset α → Prop) := fun _ _ => Classical.dec _
  refine card_mul_le_card_mul' (· ⊆ ·) (fun s hs => ?_) (fun s hs => ?_)
  · rw [← h𝒜 hs, ← card_image_of_injOn s.erase_injOn]
    refine card_le_card ?_
    simp_rw [image_subset_iff, mem_bipartiteBelow]
    exact fun a ha => ⟨erase_mem_shadow hs ha, erase_subset _ _⟩
  refine le_trans ?_ tsub_tsub_le_tsub_add
  rw [← (Set.Sized.shadow h𝒜) hs, ← card_compl, ← card_image_of_injOn (insert_inj_on' _)]
  refine card_le_card fun t ht => ?_
  -- Porting note: commented out the following line
  -- infer_instance
  rw [mem_bipartiteAbove] at ht
  have : ∅ ∉ 𝒜 := by
    rw [← mem_coe, h𝒜.empty_mem_iff, coe_eq_singleton]
    rintro rfl
    rw [shadow_singleton_empty] at hs
    exact not_mem_empty s hs
  have h := exists_eq_insert_iff.2 ⟨ht.2, by
    rw [(sized_shadow_iff this).1 (Set.Sized.shadow h𝒜) ht.1, (Set.Sized.shadow h𝒜) hs]⟩
  rcases h with ⟨a, ha, rfl⟩
  exact mem_image_of_mem _ (mem_compl.2 ha)

-- DISSOLVED: card_div_choose_le_card_shadow_div_choose

end LocalLYM

/-! ### LYM inequality -/

section LYM

section Falling

variable [DecidableEq α] (k : ℕ) (𝒜 : Finset (Finset α))

def falling : Finset (Finset α) :=
  𝒜.sup <| powersetCard k

variable {𝒜 k} {s : Finset α}

theorem mem_falling : s ∈ falling k 𝒜 ↔ (∃ t ∈ 𝒜, s ⊆ t) ∧ #s = k := by
  simp_rw [falling, mem_sup, mem_powersetCard]
  aesop

variable (𝒜 k)

theorem sized_falling : (falling k 𝒜 : Set (Finset α)).Sized k := fun _ hs => (mem_falling.1 hs).2

theorem slice_subset_falling : 𝒜 # k ⊆ falling k 𝒜 := fun s hs =>
  mem_falling.2 <| (mem_slice.1 hs).imp_left fun h => ⟨s, h, Subset.refl _⟩

theorem falling_zero_subset : falling 0 𝒜 ⊆ {∅} :=
  subset_singleton_iff'.2 fun _ ht => card_eq_zero.1 <| sized_falling _ _ ht

theorem slice_union_shadow_falling_succ : 𝒜 # k ∪ ∂ (falling (k + 1) 𝒜) = falling k 𝒜 := by
  ext s
  simp_rw [mem_union, mem_slice, mem_shadow_iff, mem_falling]
  constructor
  · rintro (h | ⟨s, ⟨⟨t, ht, hst⟩, hs⟩, a, ha, rfl⟩)
    · exact ⟨⟨s, h.1, Subset.refl _⟩, h.2⟩
    refine ⟨⟨t, ht, (erase_subset _ _).trans hst⟩, ?_⟩
    rw [card_erase_of_mem ha, hs]
    rfl
  · rintro ⟨⟨t, ht, hst⟩, hs⟩
    by_cases h : s ∈ 𝒜
    · exact Or.inl ⟨h, hs⟩
    obtain ⟨a, ha, hst⟩ := ssubset_iff.1 (ssubset_of_subset_of_ne hst (ht.ne_of_not_mem h).symm)
    refine Or.inr ⟨insert a s, ⟨⟨t, ht, hst⟩, ?_⟩, a, mem_insert_self _ _, erase_insert ha⟩
    rw [card_insert_of_not_mem ha, hs]

variable {𝒜 k}

theorem IsAntichain.disjoint_slice_shadow_falling {m n : ℕ}
    (h𝒜 : IsAntichain (· ⊆ ·) (𝒜 : Set (Finset α))) : Disjoint (𝒜 # m) (∂ (falling n 𝒜)) :=
  disjoint_right.2 fun s h₁ h₂ => by
    simp_rw [mem_shadow_iff, mem_falling] at h₁
    obtain ⟨s, ⟨⟨t, ht, hst⟩, _⟩, a, ha, rfl⟩ := h₁
    refine h𝒜 (slice_subset h₂) ht ?_ ((erase_subset _ _).trans hst)
    rintro rfl
    exact not_mem_erase _ _ (hst ha)

theorem le_card_falling_div_choose [Fintype α] (hk : k ≤ Fintype.card α)
    (h𝒜 : IsAntichain (· ⊆ ·) (𝒜 : Set (Finset α))) :
    (∑ r ∈ range (k + 1),
        (#(𝒜 # (Fintype.card α - r)) : 𝕜) / (Fintype.card α).choose (Fintype.card α - r)) ≤
      (falling (Fintype.card α - k) 𝒜).card / (Fintype.card α).choose (Fintype.card α - k) := by
  induction' k with k ih
  · simp only [tsub_zero, cast_one, cast_le, sum_singleton, div_one, choose_self, range_one,
      zero_eq, zero_add, range_one, sum_singleton, nonpos_iff_eq_zero, tsub_zero,
      choose_self, cast_one, div_one, cast_le]
    exact card_le_card (slice_subset_falling _ _)
  rw [sum_range_succ, ← slice_union_shadow_falling_succ,
    card_union_of_disjoint (IsAntichain.disjoint_slice_shadow_falling h𝒜), cast_add, _root_.add_div,
    add_comm]
  rw [← tsub_tsub, tsub_add_cancel_of_le (le_tsub_of_add_le_left hk)]
  exact
    add_le_add_left
      ((ih <| le_of_succ_le hk).trans <|
        card_div_choose_le_card_shadow_div_choose (tsub_pos_iff_lt.2 <| Nat.succ_le_iff.1 hk).ne' <|
          sized_falling _ _) _

end Falling

variable {𝒜 : Finset (Finset α)}

theorem sum_card_slice_div_choose_le_one [Fintype α]
    (h𝒜 : IsAntichain (· ⊆ ·) (𝒜 : Set (Finset α))) :
    (∑ r ∈ range (Fintype.card α + 1), (#(𝒜 # r) : 𝕜) / (Fintype.card α).choose r) ≤ 1 := by
  classical
    rw [← sum_flip]
    refine (le_card_falling_div_choose le_rfl h𝒜).trans ?_
    rw [div_le_iff₀] <;> norm_cast
    · simpa only [Nat.sub_self, one_mul, Nat.choose_zero_right, falling] using
        Set.Sized.card_le (sized_falling 0 𝒜)
    · rw [tsub_self, choose_zero_right]
      exact zero_lt_one

end LYM

/-! ### Sperner's theorem -/

theorem IsAntichain.sperner [Fintype α] {𝒜 : Finset (Finset α)}
    (h𝒜 : IsAntichain (· ⊆ ·) (𝒜 : Set (Finset α))) :
    #𝒜 ≤ (Fintype.card α).choose (Fintype.card α / 2) := by
  classical
    suffices (∑ r ∈ Iic (Fintype.card α),
        (#(𝒜 # r) : ℚ) / (Fintype.card α).choose (Fintype.card α / 2)) ≤ 1 by
      rw [← sum_div, ← Nat.cast_sum, div_le_one] at this
      · simp only [cast_le] at this
        rwa [sum_card_slice] at this
      simp only [cast_pos]
      exact choose_pos (Nat.div_le_self _ _)
    rw [Iic_eq_Icc, ← Ico_succ_right, bot_eq_zero, Ico_zero_eq_range]
    refine (sum_le_sum fun r hr => ?_).trans (sum_card_slice_div_choose_le_one h𝒜)
    rw [mem_range] at hr
    refine div_le_div_of_nonneg_left ?_ ?_ ?_ <;> norm_cast
    · exact Nat.zero_le _
    · exact choose_pos (Nat.lt_succ_iff.1 hr)
    · exact choose_le_middle _ _

end Finset
