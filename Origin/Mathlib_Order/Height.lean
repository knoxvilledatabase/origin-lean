/-
Extracted from Order/Height.lean
Genuine: 11 of 12 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!

# Maximal length of chains

This file contains lemmas to work with the maximal lengths of chains of arbitrary relations. See
`Order.height` for a definition specialized to finding the height of an element in a preorder.

## Main definition

- `Set.chainHeight`: The maximal length of a chain in a set `s` with relation `r`.

## Main results

- `Set.exists_isChain_of_le_chainHeight`: For each `n : ℕ` such that `n ≤ s.chainHeight`, there
  exists a subset `t` of length `n` such that `IsChain r t`.
- `Set.chainHeight_mono`: If `s ⊆ t` then `s.chainHeight ≤ t.chainHeight`.
- `Set.chainHeight_eq_of_relEmbedding`: If `f` is an relation embedding, then
  `(f '' s).chainHeight = s.chainHeight`.

-/

assert_not_exists Field

namespace Set

open ENat

variable {α β : Type*} (s : Set α) (r : α → α → Prop)

noncomputable def chainHeight : ℕ∞ := ⨆ t : {t : Set α // t ⊆ s ∧ IsChain r t}, t.val.encard

theorem chainHeight_le_encard : s.chainHeight r ≤ s.encard := by
  simp_all [chainHeight, encard_le_encard]

theorem chainHeight_ne_top_of_finite (h : s.Finite) : s.chainHeight r ≠ ⊤ :=
  LT.lt.ne_top <| lt_of_le_of_lt (chainHeight_le_encard s r) <| lt_top_iff_ne_top.mpr <|
    encard_ne_top_iff.mpr h

theorem exists_isChain_of_le_chainHeight {r} {s : Set α} (n : ℕ) (h : n ≤ s.chainHeight r) :
    ∃ t ⊆ s, t.encard = n ∧ IsChain r t := by
  by_cases h' : n = 0
  · exact ⟨∅, by simp [h']⟩
  · obtain ⟨t, ht₁, ht₂, ht₃⟩ : ∃ t ⊆ s, IsChain r t ∧ n ≤ t.encard := by
      contrapose! h
      refine iSup_lt_iff.mpr ⟨n - 1, ?_, fun m ↦ ENat.le_sub_one_of_lt <| h m.1 m.2.1 m.2.2⟩
      exact_mod_cast Nat.sub_one_lt h'
    obtain ⟨u, hu₁, hu₂⟩ := exists_subset_encard_eq ht₃
    exact ⟨u, hu₁.trans ht₁, hu₂, ht₂.mono hu₁⟩

theorem exists_eq_chainHeight_of_chainHeight_ne_top (h : s.chainHeight r ≠ ⊤) :
    ∃ t ⊆ s, t.encard = s.chainHeight r ∧ IsChain r t := by
  have : Nonempty { t // t ⊆ s ∧ IsChain r t } := ⟨∅, by simp⟩
  obtain ⟨t, ht⟩ := exists_eq_iSup_of_lt_top (by rwa [← chainHeight_eq_iSup, lt_top_iff_ne_top])
  exact ⟨t.1, t.2.1, ht, t.2.2⟩

theorem exists_eq_chainHeight_of_finite (h : s.Finite) :
     ∃ t ⊆ s, t.encard = s.chainHeight r ∧ IsChain r t :=
  exists_eq_chainHeight_of_chainHeight_ne_top s r (chainHeight_ne_top_of_finite s r h)

theorem encard_le_chainHeight_of_isChain {r} (s t : Set α) (hs : t ⊆ s) (hc : IsChain r t) :
    t.encard ≤ s.chainHeight r :=
  le_iSup_iff.mpr fun _ hb ↦ hb ⟨t, hs, hc⟩

theorem encard_eq_chainHeight_of_isChain {r} (s : Set α) (hc : IsChain r s) :
    s.encard = s.chainHeight r :=
  le_antisymm (encard_le_chainHeight_of_isChain _ _ Set.Subset.rfl hc) (chainHeight_le_encard _ _)

theorem finite_of_chainHeight_ne_top {r} {s : Set α} (hc : IsChain r s) (h : s.chainHeight r ≠ ⊤) :
    s.Finite :=
  Set.encard_ne_top_iff.mp <| ne_top_of_le_ne_top h <|
    encard_le_chainHeight_of_isChain _ _ (subset_refl _) hc

theorem not_isChain_of_chainHeight_lt_encard (s t : Set α) (ht : t ⊆ s)
    (he : s.chainHeight r < t.encard) : ¬ IsChain r t := by
  by_contra! hh
  grw [encard_le_chainHeight_of_isChain _ _ ht hh] at he
  exact (lt_self_iff_false _).mp he

set_option backward.isDefEq.respectTransparency false in

theorem chainHeight_eq_top_iff :
    s.chainHeight r = ⊤ ↔ ∀ n : ℕ, ∃ t ⊆ s, t.encard = n ∧ IsChain r t := by
  refine ⟨fun h _ ↦ exists_isChain_of_le_chainHeight _ (le_top.trans_eq h.symm), fun h ↦ ?_⟩
  contrapose! h
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 h
  refine ⟨n + 1, fun l hl he ↦ not_isChain_of_chainHeight_lt_encard r s l hl ?_⟩
  rw [← hn, some_eq_coe, he, Nat.cast_lt]
  exact lt_add_one _
