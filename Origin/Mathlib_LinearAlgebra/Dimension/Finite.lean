/-
Extracted from LinearAlgebra/Dimension/Finite.lean
Genuine: 10 of 13 | Dissolved: 3 | Infrastructure: 0
-/
import Origin.Core

/-!
# Conditions for rank to be finite

Also contains characterization for when rank equals zero or rank equals one.

-/

noncomputable section

universe u v v' w

variable {R : Type u} {M : Type v} {ι : Type w}

variable [Semiring R] [AddCommMonoid M]

variable [Module R M]

attribute [local instance] nontrivial_of_invariantBasisNumber

open Basis Cardinal Function Module Set Submodule

theorem linearIndependent_bounded_of_finset_linearIndependent_bounded {n : ℕ}
    (H : ∀ s : Finset M, (LinearIndependent R fun i : s => (i : M)) → s.card ≤ n) :
    ∀ s : Set M, LinearIndependent R ((↑) : s → M) → #s ≤ n := by
  intro s li
  apply Cardinal.card_le_of
  intro t
  rw [← Finset.card_map (Embedding.subtype (· ∈ s))]
  apply H
  apply linearIndependent_finset_map_embedding_subtype _ li

theorem rank_le {n : ℕ}
    (H : ∀ s : Finset M, (LinearIndependent R fun i : s => (i : M)) → s.card ≤ n) :
    Module.rank R M ≤ n := by
  rw [Module.rank_def]
  apply ciSup_le'
  rintro ⟨s, li⟩
  exact linearIndependent_bounded_of_finset_linearIndependent_bounded H _ li

section RankZero

-- DISSOLVED: rank_eq_zero_iff

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

variable [IsDomain R] [IsTorsionFree R M]

theorem rank_zero_iff_forall_zero :
    Module.rank R M = 0 ↔ ∀ x : M, x = 0 := by
  simp_rw [rank_eq_zero_iff, smul_eq_zero, and_or_left, not_and_self_iff, false_or,
    exists_and_right, and_iff_right (exists_ne (0 : R))]

theorem rank_zero_iff : Module.rank R M = 0 ↔ Subsingleton M :=
  rank_zero_iff_forall_zero.trans (subsingleton_iff_forall_eq 0).symm

-- DISSOLVED: rank_pos_iff_exists_ne_zero

theorem rank_pos_iff_nontrivial : 0 < Module.rank R M ↔ Nontrivial M :=
  rank_pos_iff_exists_ne_zero.trans (nontrivial_iff_exists_ne 0).symm

theorem rank_pos [Nontrivial M] : 0 < Module.rank R M :=
  rank_pos_iff_nontrivial.mpr ‹_›

theorem Module.finite_of_rank_eq_zero (h : Module.rank R M = 0) : Module.Finite R M := by
  nontriviality R
  rw [rank_zero_iff] at h
  infer_instance

end

-- DISSOLVED: exists_mem_ne_zero_of_rank_pos

end RankZero

section Finite

theorem Module.finite_of_rank_eq_nat [Module.Free R M] {n : ℕ} (h : Module.rank R M = n) :
    Module.Finite R M := by
  nontriviality R
  obtain ⟨⟨ι, b⟩⟩ := Module.Free.exists_basis (R := R) (M := M)
  have := mk_lt_aleph0_iff.mp <|
    b.linearIndependent.cardinal_le_rank |>.trans_eq h |>.trans_lt natCast_lt_aleph0
  exact Module.Finite.of_basis b

theorem Module.finite_of_rank_eq_one [Module.Free R M] (h : Module.rank R M = 1) :
    Module.Finite R M :=
  Module.finite_of_rank_eq_nat <| h.trans Nat.cast_one.symm

variable [StrongRankCondition R]

theorem Module.Basis.nonempty_fintype_index_of_rank_lt_aleph0 {ι : Type*} (b : Basis ι R M)
    (h : Module.rank R M < ℵ₀) : Nonempty (Fintype ι) := by
  rwa [← Cardinal.lift_lt, ← b.mk_eq_rank, Cardinal.lift_aleph0, Cardinal.lift_lt_aleph0,
    Cardinal.lt_aleph0_iff_fintype] at h
