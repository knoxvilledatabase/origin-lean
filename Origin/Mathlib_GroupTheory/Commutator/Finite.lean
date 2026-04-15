/-
Extracted from GroupTheory/Commutator/Finite.lean
Genuine: 6 of 11 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-!
The commutator of a finite direct product is contained in the direct product of the commutators.
-/

variable {G : Type*} [Group G]

namespace Subgroup

theorem commutator_pi_pi_of_finite {η : Type*} [Finite η] {Gs : η → Type*} [∀ i, Group (Gs i)]
    (H K : ∀ i, Subgroup (Gs i)) : ⁅Subgroup.pi Set.univ H, Subgroup.pi Set.univ K⁆ =
    Subgroup.pi Set.univ fun i => ⁅H i, K i⁆ := by
  classical
    apply le_antisymm (commutator_pi_pi_le H K)
    rw [pi_le_iff]
    intro i hi
    rw [map_commutator]
    apply commutator_mono <;>
      · rw [le_pi_iff]
        intro j _hj
        rintro _ ⟨x, hx, rfl⟩
        by_cases h : j = i
        · subst h
          simpa using hx
        · simp [h, one_mem]

variable [Finite (commutatorSet G)]

-- INSTANCE (free from Core): :

variable (G) in

lemma rank_commutator_le_card : Group.rank (_root_.commutator G) ≤ Nat.card (commutatorSet G) := by
  rw [Subgroup.rank_congr (commutator_eq_closure G)]
  apply Subgroup.rank_closure_finite_le_nat_card

variable [Group.FG G]

-- INSTANCE (free from Core): finiteIndex_center

variable (G) in

lemma index_center_le_pow : (center G).index ≤ Nat.card (commutatorSet G) ^ Group.rank G := by
  obtain ⟨S, hS1, hS2⟩ := Group.rank_spec G
  rw [← hS1, ← Fintype.card_coe, ← Nat.card_eq_fintype_card, ← Finset.coe_sort_coe, ← Nat.card_fun]
  exact Finite.card_le_of_embedding (quotientCenterEmbedding hS2)

end Subgroup

section commutatorRepresentatives

open Subgroup

lemma card_commutatorSet_closureCommutatorRepresentatives :
    Nat.card (commutatorSet (closureCommutatorRepresentatives G)) = Nat.card (commutatorSet G) := by
  rw [← image_commutatorSet_closureCommutatorRepresentatives G]
  exact Nat.card_congr (Equiv.Set.image _ _ (subtype_injective _))

lemma card_commutator_closureCommutatorRepresentatives :
    Nat.card (commutator (closureCommutatorRepresentatives G)) = Nat.card (commutator G) := by
  rw [commutator_eq_closure G, ← image_commutatorSet_closureCommutatorRepresentatives, ←
    MonoidHom.map_closure, ← commutator_eq_closure]
  exact Nat.card_congr (Equiv.Set.image _ _ (subtype_injective _))

variable [Finite (commutatorSet G)]

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): closureCommutatorRepresentatives_fg

variable (G) in

lemma rank_closureCommutatorRepresentatives_le :
    Group.rank (closureCommutatorRepresentatives G) ≤ 2 * Nat.card (commutatorSet G) := by
  rw [two_mul]
  exact
    (Subgroup.rank_closure_finite_le_nat_card _).trans
      ((Set.card_union_le _ _).trans
        (add_le_add ((Finite.card_image_le _).trans (Finite.card_range_le _))
          ((Finite.card_image_le _).trans (Finite.card_range_le _))))

-- INSTANCE (free from Core): :

end commutatorRepresentatives
