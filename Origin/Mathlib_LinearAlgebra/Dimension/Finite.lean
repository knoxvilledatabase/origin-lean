/-
Extracted from LinearAlgebra/Dimension/Finite.lean
Genuine: 52 of 63 | Dissolved: 9 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.Algebra.Module.Torsion
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Conditions for rank to be finite

Also contains characterization for when rank equals zero or rank equals one.

-/

noncomputable section

universe u v v' w

variable {R : Type u} {M M₁ : Type v} {M' : Type v'} {ι : Type w}

variable [Ring R] [AddCommGroup M] [AddCommGroup M'] [AddCommGroup M₁]

variable [Module R M] [Module R M'] [Module R M₁]

attribute [local instance] nontrivial_of_invariantBasisNumber

open Basis Cardinal Function Module Set Submodule

theorem rank_le {n : ℕ}
    (H : ∀ s : Finset M, (LinearIndependent R fun i : s => (i : M)) → s.card ≤ n) :
    Module.rank R M ≤ n := by
  rw [Module.rank_def]
  apply ciSup_le'
  rintro ⟨s, li⟩
  exact linearIndependent_bounded_of_finset_linearIndependent_bounded H _ li

section RankZero

-- DISSOLVED: rank_eq_zero_iff

variable [Nontrivial R]

section

variable [NoZeroSMulDivisors R M]

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

end

lemma rank_eq_zero_iff_isTorsion {R M} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M] :
    Module.rank R M = 0 ↔ Module.IsTorsion R M := by
  rw [Module.IsTorsion, rank_eq_zero_iff]
  simp [mem_nonZeroDivisors_iff_ne_zero]

variable (R M)

theorem rank_subsingleton' [Subsingleton M] : Module.rank R M = 0 :=
  rank_eq_zero_iff.mpr fun _ ↦ ⟨1, one_ne_zero, Subsingleton.elim _ _⟩

@[simp]
theorem rank_punit : Module.rank R PUnit = 0 := rank_subsingleton' _ _

@[simp]
theorem rank_bot : Module.rank R (⊥ : Submodule R M) = 0 := rank_subsingleton' _ _

variable {R M}

-- DISSOLVED: exists_mem_ne_zero_of_rank_pos

end RankZero

section Finite

theorem Module.finite_of_rank_eq_nat [Module.Free R M] {n : ℕ} (h : Module.rank R M = n) :
    Module.Finite R M := by
  nontriviality R
  obtain ⟨⟨ι, b⟩⟩ := Module.Free.exists_basis (R := R) (M := M)
  have := mk_lt_aleph0_iff.mp <|
    b.linearIndependent.cardinal_le_rank |>.trans_eq h |>.trans_lt <| nat_lt_aleph0 n
  exact Module.Finite.of_basis b

theorem Module.finite_of_rank_eq_zero [NoZeroSMulDivisors R M]
    (h : Module.rank R M = 0) :
    Module.Finite R M := by
  nontriviality R
  rw [rank_zero_iff] at h
  infer_instance

theorem Module.finite_of_rank_eq_one [Module.Free R M] (h : Module.rank R M = 1) :
    Module.Finite R M :=
  Module.finite_of_rank_eq_nat <| h.trans Nat.cast_one.symm

section

variable [StrongRankCondition R]

theorem Basis.nonempty_fintype_index_of_rank_lt_aleph0 {ι : Type*} (b : Basis ι R M)
    (h : Module.rank R M < ℵ₀) : Nonempty (Fintype ι) := by
  rwa [← Cardinal.lift_lt, ← b.mk_eq_rank, Cardinal.lift_aleph0, Cardinal.lift_lt_aleph0,
    Cardinal.lt_aleph0_iff_fintype] at h

noncomputable def Basis.fintypeIndexOfRankLtAleph0 {ι : Type*} (b : Basis ι R M)
    (h : Module.rank R M < ℵ₀) : Fintype ι :=
  Classical.choice (b.nonempty_fintype_index_of_rank_lt_aleph0 h)

theorem Basis.finite_index_of_rank_lt_aleph0 {ι : Type*} {s : Set ι} (b : Basis s R M)
    (h : Module.rank R M < ℵ₀) : s.Finite :=
  finite_def.2 (b.nonempty_fintype_index_of_rank_lt_aleph0 h)

end

namespace LinearIndependent

variable [StrongRankCondition R]

theorem cardinalMk_le_finrank [Module.Finite R M]
    {ι : Type w} {b : ι → M} (h : LinearIndependent R b) : #ι ≤ finrank R M := by
  rw [← lift_le.{max v w}]
  simpa only [← finrank_eq_rank, lift_natCast, lift_le_nat_iff] using h.cardinal_lift_le_rank

theorem fintype_card_le_finrank [Module.Finite R M]
    {ι : Type*} [Fintype ι] {b : ι → M} (h : LinearIndependent R b) :
    Fintype.card ι ≤ finrank R M := by
  simpa using h.cardinalMk_le_finrank

theorem finset_card_le_finrank [Module.Finite R M]
    {b : Finset M} (h : LinearIndependent R (fun x => x : b → M)) :
    b.card ≤ finrank R M := by
  rw [← Fintype.card_coe]
  exact h.fintype_card_le_finrank

theorem lt_aleph0_of_finite {ι : Type w}
    [Module.Finite R M] {v : ι → M} (h : LinearIndependent R v) : #ι < ℵ₀ := by
  apply Cardinal.lift_lt.1
  apply lt_of_le_of_lt
  · apply h.cardinal_lift_le_rank
  · rw [← finrank_eq_rank, Cardinal.lift_aleph0, Cardinal.lift_natCast]
    apply Cardinal.nat_lt_aleph0

theorem finite [Module.Finite R M] {ι : Type*} {f : ι → M}
    (h : LinearIndependent R f) : Finite ι :=
  Cardinal.lt_aleph0_iff_finite.1 <| h.lt_aleph0_of_finite

theorem setFinite [Module.Finite R M] {b : Set M}
    (h : LinearIndependent R fun x : b => (x : M)) : b.Finite :=
  Cardinal.lt_aleph0_iff_set_finite.mp h.lt_aleph0_of_finite

end LinearIndependent

lemma exists_set_linearIndependent_of_lt_rank {n : Cardinal} (hn : n < Module.rank R M) :
    ∃ s : Set M, #s = n ∧ LinearIndependent R ((↑) : s → M) := by
  obtain ⟨⟨s, hs⟩, hs'⟩ := exists_lt_of_lt_ciSup' (hn.trans_eq (Module.rank_def R M))
  obtain ⟨t, ht, ht'⟩ := le_mk_iff_exists_subset.mp hs'.le
  exact ⟨t, ht', .mono ht hs⟩

lemma exists_finset_linearIndependent_of_le_rank {n : ℕ} (hn : n ≤ Module.rank R M) :
    ∃ s : Finset M, s.card = n ∧ LinearIndependent R ((↑) : s → M) := by
  have := nonempty_linearIndependent_set
  cases' hn.eq_or_lt with h h
  · obtain ⟨⟨s, hs⟩, hs'⟩ := Cardinal.exists_eq_natCast_of_iSup_eq _
      (Cardinal.bddAbove_range _) _ (h.trans (Module.rank_def R M)).symm
    have : Finite s := lt_aleph0_iff_finite.mp (hs' ▸ nat_lt_aleph0 n)
    cases nonempty_fintype s
    exact ⟨s.toFinset, by simpa using hs', by convert hs using 3 <;> exact Set.mem_toFinset⟩
  · obtain ⟨s, hs, hs'⟩ := exists_set_linearIndependent_of_lt_rank h
    have : Finite s := lt_aleph0_iff_finite.mp (hs ▸ nat_lt_aleph0 n)
    cases nonempty_fintype s
    exact ⟨s.toFinset, by simpa using hs, by convert hs' using 3 <;> exact Set.mem_toFinset⟩

lemma exists_linearIndependent_of_le_rank {n : ℕ} (hn : n ≤ Module.rank R M) :
    ∃ f : Fin n → M, LinearIndependent R f :=
  have ⟨_, hs, hs'⟩ := exists_finset_linearIndependent_of_le_rank hn
  ⟨_, (linearIndependent_equiv (Finset.equivFinOfCardEq hs).symm).mpr hs'⟩

lemma natCast_le_rank_iff [Nontrivial R] {n : ℕ} :
    n ≤ Module.rank R M ↔ ∃ f : Fin n → M, LinearIndependent R f :=
  ⟨exists_linearIndependent_of_le_rank,
    fun H ↦ by simpa using H.choose_spec.cardinal_lift_le_rank⟩

lemma natCast_le_rank_iff_finset [Nontrivial R] {n : ℕ} :
    n ≤ Module.rank R M ↔ ∃ s : Finset M, s.card = n ∧ LinearIndependent R ((↑) : s → M) :=
  ⟨exists_finset_linearIndependent_of_le_rank,
    fun ⟨s, h₁, h₂⟩ ↦ by simpa [h₁] using h₂.cardinal_le_rank⟩

lemma exists_finset_linearIndependent_of_le_finrank {n : ℕ} (hn : n ≤ finrank R M) :
    ∃ s : Finset M, s.card = n ∧ LinearIndependent R ((↑) : s → M) := by
  by_cases h : finrank R M = 0
  · rw [le_zero_iff.mp (hn.trans_eq h)]
    exact ⟨∅, rfl, by convert linearIndependent_empty R M using 2 <;> aesop⟩
  exact exists_finset_linearIndependent_of_le_rank
    ((Nat.cast_le.mpr hn).trans_eq (cast_toNat_of_lt_aleph0 (toNat_ne_zero.mp h).2))

lemma exists_linearIndependent_of_le_finrank {n : ℕ} (hn : n ≤ finrank R M) :
    ∃ f : Fin n → M, LinearIndependent R f :=
  have ⟨_, hs, hs'⟩ := exists_finset_linearIndependent_of_le_finrank hn
  ⟨_, (linearIndependent_equiv (Finset.equivFinOfCardEq hs).symm).mpr hs'⟩

variable [Module.Finite R M] [StrongRankCondition R] in

theorem Module.Finite.not_linearIndependent_of_infinite {ι : Type*} [Infinite ι]
    (v : ι → M) : ¬LinearIndependent R v := mt LinearIndependent.finite <| @not_finite _ _

section

variable [NoZeroSMulDivisors R M]

theorem iSupIndep.subtype_ne_bot_le_rank [Nontrivial R]
    {V : ι → Submodule R M} (hV : iSupIndep V) :
    Cardinal.lift.{v} #{ i : ι // V i ≠ ⊥ } ≤ Cardinal.lift.{w} (Module.rank R M) := by
  set I := { i : ι // V i ≠ ⊥ }
  have hI : ∀ i : I, ∃ v ∈ V i, v ≠ (0 : M) := by
    intro i
    rw [← Submodule.ne_bot_iff]
    exact i.prop
  choose v hvV hv using hI
  have : LinearIndependent R v := (hV.comp Subtype.coe_injective).linearIndependent _ hvV hv
  exact this.cardinal_lift_le_rank

alias CompleteLattice.Independent.subtype_ne_bot_le_rank := iSupIndep.subtype_ne_bot_le_rank

variable [Module.Finite R M] [StrongRankCondition R]

theorem iSupIndep.subtype_ne_bot_le_finrank_aux
    {p : ι → Submodule R M} (hp : iSupIndep p) :
    #{ i // p i ≠ ⊥ } ≤ (finrank R M : Cardinal.{w}) := by
  suffices Cardinal.lift.{v} #{ i // p i ≠ ⊥ } ≤ Cardinal.lift.{v} (finrank R M : Cardinal.{w}) by
    rwa [Cardinal.lift_le] at this
  calc
    Cardinal.lift.{v} #{ i // p i ≠ ⊥ } ≤ Cardinal.lift.{w} (Module.rank R M) :=
      hp.subtype_ne_bot_le_rank
    _ = Cardinal.lift.{w} (finrank R M : Cardinal.{v}) := by rw [finrank_eq_rank]
    _ = Cardinal.lift.{v} (finrank R M : Cardinal.{w}) := by simp

noncomputable def iSupIndep.fintypeNeBotOfFiniteDimensional
    {p : ι → Submodule R M} (hp : iSupIndep p) :
    Fintype { i : ι // p i ≠ ⊥ } := by
  suffices #{ i // p i ≠ ⊥ } < (ℵ₀ : Cardinal.{w}) by
    rw [Cardinal.lt_aleph0_iff_fintype] at this
    exact this.some
  refine lt_of_le_of_lt hp.subtype_ne_bot_le_finrank_aux ?_
  simp [Cardinal.nat_lt_aleph0]

theorem iSupIndep.subtype_ne_bot_le_finrank
    {p : ι → Submodule R M} (hp : iSupIndep p) [Fintype { i // p i ≠ ⊥ }] :
    Fintype.card { i // p i ≠ ⊥ } ≤ finrank R M := by simpa using hp.subtype_ne_bot_le_finrank_aux

end

variable [Module.Finite R M] [StrongRankCondition R]

section

open Finset

-- DISSOLVED: Module.exists_nontrivial_relation_of_finrank_lt_card

-- DISSOLVED: Module.exists_nontrivial_relation_sum_zero_of_finrank_succ_lt_card

end

end Finite

section FinrankZero

section

variable [Nontrivial R]

@[nontriviality]
theorem Module.finrank_zero_of_subsingleton [Subsingleton M] :
    finrank R M = 0 := by
  rw [finrank, rank_subsingleton', _root_.map_zero]

lemma LinearIndependent.finrank_eq_zero_of_infinite {ι} [Infinite ι] {v : ι → M}
    (hv : LinearIndependent R v) : finrank R M = 0 := toNat_eq_zero.mpr <| .inr hv.aleph0_le_rank

section

variable [NoZeroSMulDivisors R M]

theorem Module.nontrivial_of_finrank_pos (h : 0 < finrank R M) : Nontrivial M :=
  rank_pos_iff_nontrivial.mp (lt_rank_of_lt_finrank h)

theorem Module.nontrivial_of_finrank_eq_succ {n : ℕ}
    (hn : finrank R M = n.succ) : Nontrivial M :=
  nontrivial_of_finrank_pos (R := R) (by rw [hn]; exact n.succ_pos)

end

variable (R M)

@[simp]
theorem finrank_bot : finrank R (⊥ : Submodule R M) = 0 :=
  finrank_eq_of_rank_eq (rank_bot _ _)

end

section StrongRankCondition

variable [StrongRankCondition R] [Module.Finite R M]

-- DISSOLVED: Module.finrank_pos_iff_exists_ne_zero

theorem Module.finrank_pos_iff [NoZeroSMulDivisors R M] :
    0 < finrank R M ↔ Nontrivial M := by
  rw [← rank_pos_iff_nontrivial (R := R), ← finrank_eq_rank]
  norm_cast

theorem Module.finrank_pos [NoZeroSMulDivisors R M] [h : Nontrivial M] :
    0 < finrank R M :=
  finrank_pos_iff.mpr h

-- DISSOLVED: Module.finrank_eq_zero_iff

theorem Module.finrank_eq_zero_iff_isTorsion {R} [CommRing R] [StrongRankCondition R]
    [IsDomain R] [Module R M] [Module.Finite R M] :
    finrank R M = 0 ↔ Module.IsTorsion R M := by
  rw [← rank_eq_zero_iff_isTorsion (R := R), ← finrank_eq_rank]
  norm_cast

theorem Module.finrank_zero_iff [NoZeroSMulDivisors R M] :
    finrank R M = 0 ↔ Subsingleton M := by
  rw [← rank_zero_iff (R := R), ← finrank_eq_rank]
  norm_cast

lemma Module.finrank_quotient_add_finrank_le (N : Submodule R M) :
    finrank R (M ⧸ N) + finrank R N ≤ finrank R M := by
  haveI := nontrivial_of_invariantBasisNumber R
  have := rank_quotient_add_rank_le N
  rw [← finrank_eq_rank R M, ← finrank_eq_rank R, ← N.finrank_eq_rank] at this
  exact mod_cast this

end StrongRankCondition

theorem Module.finrank_eq_zero_of_rank_eq_zero (h : Module.rank R M = 0) :
    finrank R M = 0 := by
  delta finrank
  rw [h, zero_toNat]

theorem Submodule.bot_eq_top_of_rank_eq_zero [NoZeroSMulDivisors R M] (h : Module.rank R M = 0) :
    (⊥ : Submodule R M) = ⊤ := by
  nontriviality R
  rw [rank_zero_iff] at h
  subsingleton

@[simp]
theorem Submodule.rank_eq_zero [Nontrivial R] [NoZeroSMulDivisors R M] {S : Submodule R M} :
    Module.rank R S = 0 ↔ S = ⊥ :=
  ⟨fun h =>
    (Submodule.eq_bot_iff _).2 fun x hx =>
      congr_arg Subtype.val <|
        ((Submodule.eq_bot_iff _).1 <| Eq.symm <| Submodule.bot_eq_top_of_rank_eq_zero h) ⟨x, hx⟩
          Submodule.mem_top,
    fun h => by rw [h, rank_bot]⟩

@[simp]
theorem Submodule.finrank_eq_zero [StrongRankCondition R] [NoZeroSMulDivisors R M]
    {S : Submodule R M} [Module.Finite R S] :
    finrank R S = 0 ↔ S = ⊥ := by
  rw [← Submodule.rank_eq_zero, ← finrank_eq_rank, ← @Nat.cast_zero Cardinal, Nat.cast_inj]

@[simp]
lemma Submodule.one_le_finrank_iff [StrongRankCondition R] [NoZeroSMulDivisors R M]
    {S : Submodule R M} [Module.Finite R S] :
    1 ≤ finrank R S ↔ S ≠ ⊥ := by
  simp [← not_iff_not]

variable [Module.Free R M]

theorem finrank_eq_zero_of_basis_imp_not_finite
    (h : ∀ s : Set M, Basis.{v} (s : Set M) R M → ¬s.Finite) : finrank R M = 0 := by
  cases subsingleton_or_nontrivial R
  · have := Module.subsingleton R M
    exact (h ∅ ⟨LinearEquiv.ofSubsingleton _ _⟩ Set.finite_empty).elim
  obtain ⟨_, ⟨b⟩⟩ := (Module.free_iff_set R M).mp ‹_›
  have := Set.Infinite.to_subtype (h _ b)
  exact b.linearIndependent.finrank_eq_zero_of_infinite

theorem finrank_eq_zero_of_basis_imp_false (h : ∀ s : Finset M, Basis.{v} (s : Set M) R M → False) :
    finrank R M = 0 :=
  finrank_eq_zero_of_basis_imp_not_finite fun s b hs =>
    h hs.toFinset
      (by
        convert b
        simp)

theorem finrank_eq_zero_of_not_exists_basis
    (h : ¬∃ s : Finset M, Nonempty (Basis (s : Set M) R M)) : finrank R M = 0 :=
  finrank_eq_zero_of_basis_imp_false fun s b => h ⟨s, ⟨b⟩⟩

theorem finrank_eq_zero_of_not_exists_basis_finite
    (h : ¬∃ (s : Set M) (_ : Basis.{v} (s : Set M) R M), s.Finite) : finrank R M = 0 :=
  finrank_eq_zero_of_basis_imp_not_finite fun s b hs => h ⟨s, b, hs⟩

theorem finrank_eq_zero_of_not_exists_basis_finset (h : ¬∃ s : Finset M, Nonempty (Basis s R M)) :
    finrank R M = 0 :=
  finrank_eq_zero_of_basis_imp_false fun s b => h ⟨s, ⟨b⟩⟩

end FinrankZero

section RankOne

variable [NoZeroSMulDivisors R M] [StrongRankCondition R]

-- DISSOLVED: rank_eq_one

-- DISSOLVED: finrank_eq_one

theorem finrank_le_one (v : M) (h : ∀ w : M, ∃ c : R, c • v = w) : finrank R M ≤ 1 := by
  haveI := nontrivial_of_invariantBasisNumber R
  rcases eq_or_ne v 0 with (rfl | hn)
  · haveI :=
      _root_.subsingleton_of_forall_eq (0 : M) fun w => by
        obtain ⟨c, rfl⟩ := h w
        simp
    rw [finrank_zero_of_subsingleton]
    exact zero_le_one
  · exact (finrank_eq_one v hn h).le

end RankOne
