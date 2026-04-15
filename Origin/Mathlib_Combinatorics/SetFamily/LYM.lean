/-
Extracted from Combinatorics/SetFamily/LYM.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Lubell-Yamamoto-Meshalkin inequality and Sperner's theorem

This file proves the local LYM and LYM inequalities as well as Sperner's theorem.

## Main declarations

* `Finset.local_lubell_yamamoto_meshalkin_inequality_div`: Local Lubell-Yamamoto-Meshalkin
  inequality. The shadow of a set `𝒜` in a layer takes a greater proportion of its layer than `𝒜`
  does.
* `Finset.lubell_yamamoto_meshalkin_inequality_sum_card_div_choose`: Lubell-Yamamoto-Meshalkin
  inequality. The sum of densities of `𝒜` in each layer is at most `1` for any antichain `𝒜`.
* `IsAntichain.sperner`: Sperner's theorem. The size of any antichain in `Finset α` is at most the
  size of the maximal layer of `Finset α`. It is a corollary of
  `lubell_yamamoto_meshalkin_inequality_sum_card_div_choose`.

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

open scoped FinsetFamily

variable {𝕜 α : Type*} [Semifield 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

namespace Finset

/-! ### Local LYM inequality -/

section LocalLYM

variable [DecidableEq α] [Fintype α] {𝒜 : Finset (Finset α)} {r : ℕ}

theorem local_lubell_yamamoto_meshalkin_inequality_mul (h𝒜 : (𝒜 : Set (Finset α)).Sized r) :
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
  rw [mem_bipartiteAbove] at ht
  have : ∅ ∉ 𝒜 := by
    rw [← mem_coe, h𝒜.empty_mem_iff, coe_eq_singleton]
    rintro rfl
    rw [shadow_singleton_empty] at hs
    exact notMem_empty s hs
  have h := exists_eq_insert_iff.2 ⟨ht.2, by
    rw [(sized_shadow_iff this).1 (Set.Sized.shadow h𝒜) ht.1, (Set.Sized.shadow h𝒜) hs]⟩
  rcases h with ⟨a, ha, rfl⟩
  exact mem_image_of_mem _ (mem_compl.2 ha)
