/-
Extracted from Data/Finset/Interval.lean
Genuine: 22 of 23 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Intervals of finsets as finsets

This file provides the `LocallyFiniteOrder` instance for `Finset α` and calculates the cardinality
of finite intervals of finsets.

If `s t : Finset α`, then `Finset.Icc s t` is the finset of finsets which include `s` and are
included in `t`. For example,
`Finset.Icc {0, 1} {0, 1, 2, 3} = {{0, 1}, {0, 1, 2}, {0, 1, 3}, {0, 1, 2, 3}}`
and
`Finset.Icc {0, 1, 2} {0, 1, 3} = {}`.

In addition, this file gives characterizations of monotone and strictly monotone functions
out of `Finset α` in terms of `Finset.insert`
-/

variable {α β : Type*}

namespace Finset

section Decidable

-- INSTANCE (free from Core): instLocallyFiniteOrder

variable [DecidableEq α] (s t : Finset α)

theorem Icc_eq_filter_powerset : Icc s t = {u ∈ t.powerset | s ⊆ u} := by ext; simp [and_comm]

theorem Ico_eq_filter_ssubsets : Ico s t = {u ∈ t.ssubsets | s ⊆ u} := by ext; simp [and_comm]

theorem Ioc_eq_filter_powerset : Ioc s t = {u ∈ t.powerset | s ⊂ u} := by ext; simp [and_comm]

theorem Ioo_eq_filter_ssubsets : Ioo s t = {u ∈ t.ssubsets | s ⊂ u} := by ext; simp [and_comm]

theorem Iic_eq_powerset : Iic s = s.powerset := by ext; simp

theorem Iio_eq_ssubsets : Iio s = s.ssubsets := by ext; simp

variable {s t}

theorem Icc_eq_image_powerset (h : s ⊆ t) : Icc s t = (t \ s).powerset.image (s ∪ ·) := by
  unfold Finset.Icc instLocallyFiniteOrder LocallyFiniteOrder.ofIcc
  ext
  simp [h, union_comm]

theorem Ico_eq_image_ssubsets (h : s ⊆ t) : Ico s t = (t \ s).ssubsets.image (s ∪ ·) := by
  ext u
  simp_rw [mem_Ico, mem_image, mem_ssubsets]
  constructor
  · rintro ⟨hs, ht⟩
    exact ⟨u \ s, sdiff_lt_sdiff_right ht hs, sup_sdiff_cancel_right hs⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨le_sup_left, sup_lt_of_lt_sdiff_left hv h⟩

theorem card_Icc_finset (h : s ⊆ t) : (Icc s t).card = 2 ^ (t.card - s.card) := by
  unfold Finset.Icc instLocallyFiniteOrder LocallyFiniteOrder.ofIcc
  simp [h, card_sdiff_of_subset]

theorem card_Ico_finset (h : s ⊆ t) : (Ico s t).card = 2 ^ (t.card - s.card) - 1 := by
  rw [card_Ico_eq_card_Icc_sub_one, card_Icc_finset h]

theorem card_Ioc_finset (h : s ⊆ t) : (Ioc s t).card = 2 ^ (t.card - s.card) - 1 := by
  rw [card_Ioc_eq_card_Icc_sub_one, card_Icc_finset h]

theorem card_Ioo_finset (h : s ⊆ t) : (Ioo s t).card = 2 ^ (t.card - s.card) - 2 := by
  rw [card_Ioo_eq_card_Icc_sub_two, card_Icc_finset h]

theorem card_Iic_finset : (Iic s).card = 2 ^ s.card := by rw [Iic_eq_powerset, card_powerset]

theorem card_Iio_finset : (Iio s).card = 2 ^ s.card - 1 := by
  rw [Iio_eq_ssubsets, ssubsets, card_erase_of_mem (mem_powerset_self _), card_powerset]

end Decidable

variable [Preorder β] {s t : Finset α} {f : Finset α → β}

section Cons

lemma monotone_iff_forall_le_cons : Monotone f ↔ ∀ s, ∀ ⦃a⦄ (ha), f s ≤ f (cons a s ha) := by
  classical simp [monotone_iff_forall_covBy, covBy_iff_exists_cons]

lemma antitone_iff_forall_cons_le : Antitone f ↔ ∀ s ⦃a⦄ ha, f (cons a s ha) ≤ f s :=
  monotone_iff_forall_le_cons (β := βᵒᵈ)

lemma strictMono_iff_forall_lt_cons : StrictMono f ↔ ∀ s ⦃a⦄ ha, f s < f (cons a s ha) := by
  classical simp [strictMono_iff_forall_covBy, covBy_iff_exists_cons]

lemma strictAnti_iff_forall_cons_lt : StrictAnti f ↔ ∀ s ⦃a⦄ ha, f (cons a s ha) < f s :=
  strictMono_iff_forall_lt_cons (β := βᵒᵈ)

end Cons

section Insert

variable [DecidableEq α]

lemma monotone_iff_forall_le_insert : Monotone f ↔ ∀ s ⦃a⦄, a ∉ s → f s ≤ f (insert a s) := by
  simp [monotone_iff_forall_le_cons]

lemma antitone_iff_forall_insert_le : Antitone f ↔ ∀ s ⦃a⦄, a ∉ s → f (insert a s) ≤ f s :=
  monotone_iff_forall_le_insert (β := βᵒᵈ)

lemma strictMono_iff_forall_lt_insert : StrictMono f ↔ ∀ s ⦃a⦄, a ∉ s → f s < f (insert a s) := by
  simp [strictMono_iff_forall_lt_cons]

lemma strictAnti_iff_forall_lt_insert : StrictAnti f ↔ ∀ s ⦃a⦄, a ∉ s → f (insert a s) < f s :=
  strictMono_iff_forall_lt_insert (β := βᵒᵈ)

end Insert

end Finset
