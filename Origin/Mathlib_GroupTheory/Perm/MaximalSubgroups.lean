/-
Extracted from GroupTheory/Perm/MaximalSubgroups.lean
Genuine: 4 of 6 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-! # Maximal subgroups of the symmetric groups

* `Equiv.Perm.isCoatom_stabilizer`:
  if neither `s : Set α` nor its complementary subset is empty,
  and the cardinality of `s` is not half of that of `α`,
  then `MulAction.stabilizer (Equiv.Perm α) s` is
  a maximal subgroup of the symmetric group `Equiv.Perm α`.

  This is the *intransitive case* of the O'Nan-Scott classification.

## TODO

  * Application to primitivity of the action
    of `Equiv.Perm α` on finite combinations of `α`.

  * Formalize the other cases of the classification.
    The next one should be the *imprimitive case*.

## Reference

The argument is taken from [M. Liebeck, C. Praeger, J. Saxl,
*A classification of the maximal subgroups of the finite
alternating and symmetric groups*, 1987][LiebeckPraegerSaxl-1987].
-/

open scoped Pointwise

open Set

variable {M α : Type*} [Group M] [MulAction M α] {s : Set α}

namespace MulAction

open Equiv

variable (s) in

theorem IsPretransitive.of_partition
    (hs : ∀ a ∈ s, ∀ b ∈ s, ∃ g : M, g • a = b)
    (hs' : ∀ a ∈ sᶜ, ∀ b ∈ sᶜ, ∃ g : M, g • a = b)
    (hM : stabilizer M s ≠ ⊤) :
    IsPretransitive M α := by
  suffices ∃ (a b : α) (g : M), a ∈ s ∧ b ∈ sᶜ ∧ g • a = b by
    obtain ⟨a, b, g, ha, hb, hgab⟩ := this
    rw [isPretransitive_iff_base a]
    intro x
    by_cases hx : x ∈ s
    · exact hs a ha x hx
    · rw [← Set.mem_compl_iff] at hx
      obtain ⟨k, hk⟩ := hs' b hb x hx
      use k * g
      rw [mul_smul, hgab, hk]
  contrapose! hM
  rw [eq_top_iff, le_stabilizer_iff_smul_le]
  rintro g _ b ⟨a, ha, hgab⟩
  by_contra hb
  exact hM a b g ha (Set.mem_compl hb) hgab

end MulAction

namespace Equiv.Perm

open MulAction

theorem ofSubtype_mem_stabilizer [DecidablePred fun x ↦ x ∈ s] (g : Perm s) :
    g.ofSubtype ∈ stabilizer (Perm α) s := by
  rw [mem_stabilizer_iff]
  ext g'
  simp_rw [mem_smul_set, Perm.smul_def]
  refine ⟨?_, fun a ↦ ?_⟩
  · rintro ⟨w, hs, rfl⟩
    simp [ofSubtype_apply_of_mem _ hs]
  · use (g⁻¹ ⟨g', a⟩)
    simp

theorem swap_mem_stabilizer [DecidableEq α]
    {a b : α} {s : Set α} (ha : a ∈ s) (hb : b ∈ s) :
    swap a b ∈ stabilizer (Perm α) s := by
  suffices swap a b • s ⊆ s by
    rw [mem_stabilizer_iff]
    apply Set.Subset.antisymm this
    exact Set.subset_smul_set_iff.mpr this
  rintro _ ⟨x, hx, rfl⟩
  by_cases h : x ∈ ({a, b} : Set α)
  · aesop
  · have := swap_apply_of_ne_of_ne (a := a) (b := b) (x := x)
    aesop

theorem exists_mem_stabilizer_smul_eq :
    ∀ a ∈ s, ∀ b ∈ s, ∃ g ∈ stabilizer (Perm α) s, g • a = b := by
  intro a ha b hb
  classical
  exact ⟨swap a b, swap_mem_stabilizer ha hb, swap_apply_left a b⟩
