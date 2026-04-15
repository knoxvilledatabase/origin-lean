/-
Extracted from FieldTheory/IntermediateField/Adjoin/Basic.lean
Genuine: 21 of 26 | Dissolved: 1 | Infrastructure: 4
-/
import Origin.Core

/-!
# Adjoining Elements to Fields

This file contains many results about adjoining elements to fields.
-/

open Module Polynomial

namespace IntermediateField

lemma restrictScalars_le_iff (K : Type*) {L E : Type*} [Field K] [Field L]
    [Field E] [Algebra K L] [Algebra K E] [Algebra L E] [IsScalarTower K L E]
    {E₁ E₂ : IntermediateField L E} : E₁.restrictScalars K ≤ E₂.restrictScalars K ↔ E₁ ≤ E₂ := .rfl

lemma FG.of_restrictScalars {K L E : Type*} [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra K E] [Algebra L E] [IsScalarTower K L E]
    {E' : IntermediateField L E} (H : (E'.restrictScalars K).FG) : E'.FG := by
  obtain ⟨s, hs⟩ := H
  refine ⟨s, le_antisymm ?_ ?_⟩
  · rw [adjoin_le_iff]
    exact (subset_adjoin K _).trans_eq congr(($hs : Set E))
  · rw [← restrictScalars_le_iff K, ← hs, adjoin_le_iff]
    exact subset_adjoin L _

end

section AdjoinDef

variable (F : Type*) [Field F] {E : Type*} [Field E] [Algebra F E] {S : Set E}

theorem mem_adjoin_range_iff {ι : Type*} (i : ι → E) (x : E) :
    x ∈ adjoin F (Set.range i) ↔ ∃ r s : MvPolynomial ι F,
      x = MvPolynomial.aeval i r / MvPolynomial.aeval i s := by
  simp_rw [mem_adjoin_iff_div, Algebra.adjoin_range_eq_range_aeval,
    AlgHom.mem_range, exists_exists_eq_and]

theorem mem_adjoin_iff (x : E) :
    x ∈ adjoin F S ↔ ∃ r s : MvPolynomial S F,
      x = MvPolynomial.aeval Subtype.val r / MvPolynomial.aeval Subtype.val s := by
  rw [← mem_adjoin_range_iff, Subtype.range_coe]

theorem mem_adjoin_simple_iff {α : E} (x : E) :
    x ∈ adjoin F {α} ↔ ∃ r s : F[X], x = aeval α r / aeval α s := by
  simp only [mem_adjoin_iff_div, Algebra.adjoin_singleton_eq_range_aeval,
    AlgHom.mem_range, exists_exists_eq_and]

theorem forall_mem_adjoin_smul_eq_self_iff {M : Type*} [Monoid M] [MulSemiringAction M E]
    [SMulCommClass M F E] (m : M) :
    (∀ x ∈ adjoin F S, m • x = x) ↔ ∀ x ∈ S, m • x = x := by
  simpa [-adjoin_le_iff, Set.subset_def, SetLike.le_def, FixedBy.intermediateField_mem_iff] using
    adjoin_le_iff (T := FixedBy.intermediateField F E m)

variable {F}

section Supremum

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (E1 E2 : IntermediateField K L)

-- INSTANCE (free from Core): finiteDimensional_sup

theorem rank_sup_le_of_isAlgebraic
    (halg : Algebra.IsAlgebraic K E1 ∨ Algebra.IsAlgebraic K E2) :
    Module.rank K ↥(E1 ⊔ E2) ≤ Module.rank K E1 * Module.rank K E2 := by
  have := E1.toSubalgebra.rank_sup_le_of_free E2.toSubalgebra
  rwa [← sup_toSubalgebra_of_isAlgebraic E1 E2 halg] at this

theorem finrank_sup_le :
    finrank K ↥(E1 ⊔ E2) ≤ finrank K E1 * finrank K E2 := by
  by_cases h : FiniteDimensional K E1
  · have := E1.toSubalgebra.finrank_sup_le_of_free E2.toSubalgebra
    change _ ≤ finrank K E1 * finrank K E2 at this
    rwa [← sup_toSubalgebra_of_left] at this
  rw [FiniteDimensional, ← rank_lt_aleph0_iff, not_lt] at h
  have := LinearMap.rank_le_of_injective _ <| Submodule.inclusion_injective <|
    show Subalgebra.toSubmodule E1.toSubalgebra ≤ Subalgebra.toSubmodule (E1 ⊔ E2).toSubalgebra by
      simp
  rw [show finrank K E1 = 0 from Cardinal.toNat_apply_of_aleph0_le h,
    show finrank K ↥(E1 ⊔ E2) = 0 from Cardinal.toNat_apply_of_aleph0_le (h.trans this), zero_mul]

variable {ι : Type*} {t : ι → IntermediateField K L}

theorem coe_iSup_of_directed [Nonempty ι] (dir : Directed (· ≤ ·) t) :
    ↑(iSup t) = ⋃ i, (t i : Set L) :=
  let M : IntermediateField K L :=
    { __ := Subalgebra.copy _ _ (Subalgebra.coe_iSup_of_directed dir).symm
      inv_mem' := fun _ hx ↦ have ⟨i, hi⟩ := Set.mem_iUnion.mp hx
        Set.mem_iUnion.mpr ⟨i, (t i).inv_mem hi⟩ }
  have : iSup t = M := le_antisymm
    (iSup_le fun i ↦ le_iSup (fun i ↦ (t i : Set L)) i) (Set.iUnion_subset fun _ ↦ le_iSup t _)
  this.symm ▸ rfl

theorem toSubalgebra_iSup_of_directed (dir : Directed (· ≤ ·) t) :
    (iSup t).toSubalgebra = ⨆ i, (t i).toSubalgebra := by
  cases isEmpty_or_nonempty ι
  · simp_rw [iSup_of_empty, bot_toSubalgebra]
  · exact SetLike.ext' ((coe_iSup_of_directed dir).trans (Subalgebra.coe_iSup_of_directed dir).symm)

-- INSTANCE (free from Core): finiteDimensional_iSup_of_finite

-- INSTANCE (free from Core): finiteDimensional_iSup_of_finset

theorem finiteDimensional_iSup_of_finset'
    {s : Finset ι} (h : ∀ i ∈ s, FiniteDimensional K (t i)) :
    FiniteDimensional K (⨆ i ∈ s, t i : IntermediateField K L) :=
  have := Subtype.forall'.mp h
  iSup_subtype'' s t ▸ IntermediateField.finiteDimensional_iSup_of_finite

-- DISSOLVED: isSplittingField_iSup

end Supremum

section Tower

variable (E)

variable {K : Type*} [Field K] [Algebra F K] [Algebra E K] [IsScalarTower F E K]

theorem adjoin_rank_le_of_isAlgebraic (L : IntermediateField F K)
    (halg : Algebra.IsAlgebraic F E ∨ Algebra.IsAlgebraic F L) :
    Module.rank E (adjoin E (L : Set K)) ≤ Module.rank F L := by
  have h : (adjoin E (L.toSubalgebra : Set K)).toSubalgebra =
      Algebra.adjoin E (L.toSubalgebra : Set K) :=
    L.adjoin_intermediateField_toSubalgebra_of_isAlgebraic E halg
  have := L.toSubalgebra.adjoin_rank_le E
  rwa [(Subalgebra.equivOfEq _ _ h).symm.toLinearEquiv.rank_eq] at this

theorem adjoin_rank_le_of_isAlgebraic_left (L : IntermediateField F K)
    [halg : Algebra.IsAlgebraic F E] :
    Module.rank E (adjoin E (L : Set K)) ≤ Module.rank F L :=
  adjoin_rank_le_of_isAlgebraic E L (Or.inl halg)

theorem adjoin_rank_le_of_isAlgebraic_right (L : IntermediateField F K)
    [halg : Algebra.IsAlgebraic F L] :
    Module.rank E (adjoin E (L : Set K)) ≤ Module.rank F L :=
  adjoin_rank_le_of_isAlgebraic E L (Or.inr halg)

end Tower

open Set CompleteLattice

theorem adjoin_simple_isCompactElement (x : E) : IsCompactElement F⟮x⟯ := by
  simp_rw [isCompactElement_iff_le_of_directed_sSup_le,
    adjoin_simple_le_iff, sSup_eq_iSup', ← exists_prop]
  intro s hne hs hx
  have := hne.to_subtype
  rwa [← SetLike.mem_coe, coe_iSup_of_directed hs.directed_val, mem_iUnion, Subtype.exists] at hx

theorem adjoin_finset_isCompactElement (S : Finset E) :
    IsCompactElement (adjoin F S : IntermediateField F E) := by
  rw [← biSup_adjoin_simple]
  simp_rw [Finset.mem_coe, ← Finset.sup_eq_iSup]
  exact isCompactElement_finsetSup S fun x _ => adjoin_simple_isCompactElement x

theorem adjoin_finite_isCompactElement {S : Set E} (h : S.Finite) : IsCompactElement (adjoin F S) :=
  Finite.coe_toFinset h ▸ adjoin_finset_isCompactElement h.toFinset

-- INSTANCE (free from Core): :

theorem exists_finset_of_mem_iSup {ι : Type*} {f : ι → IntermediateField F E} {x : E}
    (hx : x ∈ ⨆ i, f i) : ∃ s : Finset ι, x ∈ ⨆ i ∈ s, f i := by
  have := (adjoin_simple_isCompactElement x).exists_finset_of_le_iSup (IntermediateField F E) f
  simp only [adjoin_simple_le_iff] at this
  exact this hx

theorem exists_finset_of_mem_supr' {ι : Type*} {f : ι → IntermediateField F E} {x : E}
    (hx : x ∈ ⨆ i, f i) : ∃ s : Finset (Σ i, f i), x ∈ ⨆ i ∈ s, F⟮(i.2 : E)⟯ := by
  refine exists_finset_of_mem_iSup (SetLike.le_def.mp (iSup_le fun i x h ↦ ?_) hx)
  exact SetLike.le_def.mp (le_iSup_of_le ⟨i, x, h⟩ (by simp)) (mem_adjoin_simple_self F x)

theorem exists_finset_of_mem_supr'' {ι : Type*} {f : ι → IntermediateField F E}
    (h : ∀ i, Algebra.IsAlgebraic F (f i)) {x : E} (hx : x ∈ ⨆ i, f i) :
    ∃ s : Finset (Σ i, f i), x ∈ ⨆ i ∈ s, adjoin F ((minpoly F (i.2 :)).rootSet E) := by
  refine exists_finset_of_mem_iSup (SetLike.le_def.mp (iSup_le (fun i x1 hx1 => ?_)) hx)
  refine SetLike.le_def.mp (le_iSup_of_le ⟨i, x1, hx1⟩ ?_)
    (subset_adjoin F (rootSet (minpoly F x1) E) ?_)
  · rw [IntermediateField.minpoly_eq, Subtype.coe_mk]
  · rw [mem_rootSet_of_ne, minpoly.aeval]
    exact minpoly.ne_zero (isIntegral_iff.mp (Algebra.IsIntegral.isIntegral (⟨x1, hx1⟩ : f i)))

theorem exists_finset_of_mem_adjoin {S : Set E} {x : E} (hx : x ∈ adjoin F S) :
    ∃ T : Finset E, (T : Set E) ⊆ S ∧ x ∈ adjoin F (T : Set E) := by
  simp_rw [← biSup_adjoin_simple S, ← iSup_subtype''] at hx
  obtain ⟨s, hx'⟩ := exists_finset_of_mem_iSup hx
  classical
  refine ⟨s.image Subtype.val, by simp, SetLike.le_def.mp ?_ hx'⟩
  simp_rw [Finset.coe_image, iSup_le_iff, adjoin_le_iff]
  rintro _ h _ rfl
  exact subset_adjoin F _ ⟨_, h, rfl⟩

end AdjoinDef

section AdjoinIntermediateFieldLattice

variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E] {α : E} {S : Set E}

section AdjoinRank

open Module Module

variable {K L : IntermediateField F E}
