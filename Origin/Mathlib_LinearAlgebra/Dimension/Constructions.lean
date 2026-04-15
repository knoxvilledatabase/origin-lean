/-
Extracted from LinearAlgebra/Dimension/Constructions.lean
Genuine: 8 of 8 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Rank of various constructions

## Main statements

- `rank_quotient_add_rank_le` : `rank M/N + rank N ≤ rank M`.
- `lift_rank_add_lift_rank_le_rank_prod`: `rank M × N ≤ rank M + rank N`.
- `rank_span_le_of_finite`: `rank (span s) ≤ #s` for finite `s`.

For free modules, we have

- `rank_prod` : `rank M × N = rank M + rank N`.
- `rank_finsupp` : `rank (ι →₀ M) = #ι * rank M`
- `rank_directSum`: `rank (⨁ Mᵢ) = ∑ rank Mᵢ`
- `rank_tensorProduct`: `rank (M ⊗ N) = rank M * rank N`.

Lemmas for ranks of submodules and subalgebras are also provided.
We have `finrank` variants for most lemmas as well.

-/

noncomputable section

universe u u' v v' u₁' w w'

variable {R : Type u} {S : Type u'} {M : Type v} {M' : Type v'} {M₁ : Type v}

variable {ι : Type w} {ι' : Type w'} {η : Type u₁'} {φ : η → Type*}

open Basis Cardinal DirectSum Function Module Set Submodule

section Quotient

variable [Ring R] [CommRing S] [AddCommGroup M] [AddCommGroup M'] [AddCommGroup M₁]

variable [Module R M]

theorem LinearIndependent.sumElim_of_quotient
    {M' : Submodule R M} {ι₁ ι₂} {f : ι₁ → M'} (hf : LinearIndependent R f) (g : ι₂ → M)
    (hg : LinearIndependent R (Submodule.Quotient.mk (p := M') ∘ g)) :
    LinearIndependent R (Sum.elim (f · : ι₁ → M) g) := by
  refine .sum_type (hf.map' M'.subtype M'.ker_subtype) (.of_comp M'.mkQ hg) ?_
  refine disjoint_def.mpr fun x h₁ h₂ ↦ ?_
  have : x ∈ M' := span_le.mpr (Set.range_subset_iff.mpr fun i ↦ (f i).prop) h₁
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp h₂
  simp_rw [← Quotient.mk_eq_zero, ← mkQ_apply, map_finsuppSum, map_smul, mkQ_apply] at this
  rw [linearIndependent_iff.mp hg _ this, Finsupp.sum_zero_index]

theorem LinearIndepOn.union_of_quotient {s t : Set ι} {f : ι → M} (hs : LinearIndepOn R f s)
    (ht : LinearIndepOn R (mkQ (span R (f '' s)) ∘ f) t) : LinearIndepOn R f (s ∪ t) := by
  apply hs.union ht.of_comp
  convert (Submodule.range_ker_disjoint ht).symm
  · simp
  aesop

theorem LinearIndepOn.union_id_of_quotient {M' : Submodule R M}
    {s : Set M} (hs : s ⊆ M') (hs' : LinearIndepOn R id s) {t : Set M}
    (ht : LinearIndepOn R (mkQ M') t) : LinearIndepOn R id (s ∪ t) :=
  hs'.union_of_quotient <| by
    rw [image_id]
    exact ht.of_comp ((span R s).mapQ M' (LinearMap.id) (span_le.2 hs))

theorem linearIndepOn_union_iff_quotient {s t : Set ι} {f : ι → M} (hst : Disjoint s t) :
    LinearIndepOn R f (s ∪ t) ↔
    LinearIndepOn R f s ∧ LinearIndepOn R (mkQ (span R (f '' s)) ∘ f) t := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun h ↦ h.1.union_of_quotient h.2⟩
  · exact h.mono subset_union_left
  apply (h.mono subset_union_right).map
  simpa [← image_eq_range] using ((linearIndepOn_union_iff hst).1 h).2.2.symm

theorem LinearIndepOn.quotient_iff_union {s t : Set ι} {f : ι → M} (hs : LinearIndepOn R f s)
    (hst : Disjoint s t) :
    LinearIndepOn R (mkQ (span R (f '' s)) ∘ f) t ↔ LinearIndepOn R f (s ∪ t) := by
  rw [linearIndepOn_union_iff_quotient hst, and_iff_right hs]

theorem rank_quotient_add_rank_le [Nontrivial R] (M' : Submodule R M) :
    Module.rank R (M ⧸ M') + Module.rank R M' ≤ Module.rank R M := by
  conv_lhs => simp only [Module.rank_def]
  rw [Cardinal.ciSup_add_ciSup _ (bddAbove_range _) _ (bddAbove_range _)]
  refine ciSup_le fun ⟨s, hs⟩ ↦ ciSup_le fun ⟨t, ht⟩ ↦ ?_
  choose f hf using Submodule.Quotient.mk_surjective M'
  simpa [add_comm] using (LinearIndependent.sumElim_of_quotient ht (fun (i : s) ↦ f i)
    (by simpa [Function.comp_def, hf] using hs)).cardinal_le_rank

theorem rank_quotient_le (p : Submodule R M) : Module.rank R (M ⧸ p) ≤ Module.rank R M :=
  (mkQ p).rank_le_of_surjective Quot.mk_surjective

theorem Submodule.finrank_quotient_le [StrongRankCondition R] [Module.Finite R M]
    (s : Submodule R M) : finrank R (M ⧸ s) ≤ finrank R M :=
  toNat_le_toNat ((Submodule.mkQ s).rank_le_of_surjective Quot.mk_surjective)
    (rank_lt_aleph0 _ _)

end Quotient

variable [Semiring R] [CommSemiring S] [AddCommMonoid M] [AddCommMonoid M'] [AddCommMonoid M₁]

variable [Module R M]

section ULift
