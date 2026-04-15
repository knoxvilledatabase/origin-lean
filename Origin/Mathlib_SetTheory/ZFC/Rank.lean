/-
Extracted from SetTheory/ZFC/Rank.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Ordinal ranks of PSet and ZFSet

In this file, we define the ordinal ranks of `PSet` and `ZFSet`. These ranks are the same as
`IsWellFounded.rank` over `∈`, but are defined in a way that the universe levels of ranks are the
same as the indexing types.

## Definitions

* `PSet.rank`: Ordinal rank of a pre-set.
* `ZFSet.rank`: Ordinal rank of a ZFC set.
-/

universe u v

open Ordinal Order

/-! ### PSet rank -/

namespace PSet

noncomputable def rank : PSet.{u} → Ordinal.{u}
  | ⟨_, A⟩ => ⨆ a, succ (rank (A a))

theorem rank_congr : ∀ {x y : PSet}, Equiv x y → rank x = rank y
  | ⟨_, _⟩, ⟨_, _⟩, ⟨αβ, βα⟩ => by
    apply congr_arg sSup
    ext
    constructor <;> simp only [Set.mem_range, forall_exists_index] <;> intro a h
    · obtain ⟨b, h'⟩ := αβ a
      exists b
      rw [← h, rank_congr h']
    · obtain ⟨b, h'⟩ := βα a
      exists b
      rw [← h, rank_congr h']

theorem rank_lt_of_mem : ∀ {x y : PSet}, y ∈ x → rank y < rank x
  | ⟨_, _⟩, _, ⟨_, h⟩ => by
    rw [rank_congr h, ← succ_le_iff]
    apply Ordinal.le_iSup

theorem rank_le_iff {o : Ordinal} : ∀ {x : PSet}, rank x ≤ o ↔ ∀ ⦃y⦄, y ∈ x → rank y < o
  | ⟨_, A⟩ => by
    refine ⟨fun h _ h' => (rank_lt_of_mem h').trans_le h, fun h ↦ Ordinal.iSup_le fun a ↦ ?_⟩
    rw [succ_le_iff]
    exact h (Mem.mk A a)

theorem lt_rank_iff {o : Ordinal} {x : PSet} : o < rank x ↔ ∃ y ∈ x, o ≤ rank y := by
  contrapose!; exact rank_le_iff

variable {x y : PSet.{u}}
