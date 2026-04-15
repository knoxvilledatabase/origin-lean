/-
Extracted from Data/Set/Card/Arithmetic.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Results using cardinal arithmetic

This file contains results using cardinal arithmetic that are not in the main cardinal theory files.
It has been separated out to not burden `Mathlib/Data/Set/Card.lean` with extra imports.

## Main results

- `exists_union_disjoint_ncard_eq_of_even`: Given a set `s` with an even cardinality, there exist
  disjoint sets `t` and `u` such that `t ∪ u = s` and `t.ncard = u.ncard`.
- `exists_union_disjoint_cardinal_eq_iff` is the same, except using cardinal notation.
-/

variable {α ι : Type*}

open scoped Finset

theorem Finset.exists_disjoint_union_of_even_card [DecidableEq α] {s : Finset α} (he : Even #s) :
    ∃ (t u : Finset α), t ∪ u = s ∧ Disjoint t u ∧ #t = #u :=
  let ⟨n, hn⟩ := he
  let ⟨t, ht, ht'⟩ := exists_subset_card_eq (show n ≤ #s by lia)
  ⟨t, s \ t, by simp [card_sdiff_of_subset, disjoint_sdiff, *]⟩

theorem Finset.exists_disjoint_union_of_even_card_iff [DecidableEq α] (s : Finset α) :
    Even #s ↔ ∃ (t u : Finset α), t ∪ u = s ∧ Disjoint t u ∧ #t = #u :=
  ⟨Finset.exists_disjoint_union_of_even_card, by
    rintro ⟨t, u, rfl, hdtu, hctu⟩
    simp_all⟩
