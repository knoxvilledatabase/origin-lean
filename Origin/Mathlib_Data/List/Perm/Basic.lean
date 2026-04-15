/-
Extracted from Data/List/Perm/Basic.lean
Genuine: 6 of 7 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# List Permutations

This file develops theory about the `List.Perm` relation.

## Notation

The notation `~` is used for permutation equivalence.
-/

assert_not_exists Monoid Preorder

open Nat

namespace List

variable {α β : Type*} {l : List α}

open Perm (swap)

lemma perm_rfl : l ~ l := Perm.refl _

attribute [symm] Perm.symm

attribute [trans] Perm.trans

-- INSTANCE (free from Core): :

theorem Perm.subset_congr_left {l₁ l₂ l₃ : List α} (h : l₁ ~ l₂) : l₁ ⊆ l₃ ↔ l₂ ⊆ l₃ :=
  ⟨h.symm.subset.trans, h.subset.trans⟩

theorem Perm.subset_congr_right {l₁ l₂ l₃ : List α} (h : l₁ ~ l₂) : l₃ ⊆ l₁ ↔ l₃ ⊆ l₂ :=
  ⟨fun h' => h'.trans h.subset, fun h' => h'.trans h.symm.subset⟩

theorem set_perm_cons_eraseIdx {n : ℕ} (h : n < l.length) (a : α) :
    l.set n a ~ a :: l.eraseIdx n := by
  rw [← insertIdx_eraseIdx_self (Nat.ne_of_lt h)]
  apply perm_insertIdx
  rw [length_eraseIdx_of_lt h]
  exact Nat.le_sub_one_of_lt h

theorem getElem_cons_eraseIdx_perm {n : ℕ} (h : n < l.length) :
    l[n] :: l.eraseIdx n ~ l := by
  simpa [h] using (set_perm_cons_eraseIdx h l[n]).symm

theorem perm_insertIdx_iff_of_le {l₁ l₂ : List α} {m n : ℕ} (hm : m ≤ l₁.length)
    (hn : n ≤ l₂.length) (a : α) : l₁.insertIdx m a ~ l₂.insertIdx n a ↔ l₁ ~ l₂ := by
  rw [rel_congr_left (perm_insertIdx _ _ hm), rel_congr_right (perm_insertIdx _ _ hn), perm_cons]

alias ⟨_, Perm.insertIdx_of_le⟩ := perm_insertIdx_iff_of_le
