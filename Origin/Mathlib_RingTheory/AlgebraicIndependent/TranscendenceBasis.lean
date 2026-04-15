/-
Extracted from RingTheory/AlgebraicIndependent/TranscendenceBasis.lean
Genuine: 19 of 20 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Transcendence basis

This file defines the transcendence basis as a maximal algebraically independent subset.

## Main results

* `exists_isTranscendenceBasis`: a ring extension has a transcendence basis
* `IsTranscendenceBasis.lift_cardinalMk_eq_trdeg`: any transcendence basis of a domain has
  cardinality equal to transcendental degree.
* `IsTranscendenceBasis.lift_cardinalMk_eq`: any two transcendence bases of a domain have the
  same cardinality.

## References

* [Stacks: Transcendence](https://stacks.math.columbia.edu/tag/030D)

## Tags
transcendence basis, transcendence degree, transcendence

-/

noncomputable section

open Function Set Subalgebra MvPolynomial Algebra

universe u u' v w

variable {ι : Type u} {ι' : Type u'} (R : Type*) {S : Type v} {A : Type w}

variable {x : ι → A} {y : ι' → A}

variable [CommRing R] [CommRing S] [CommRing A]

variable [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A]

open AlgebraicIndependent

variable {R} in

theorem exists_isTranscendenceBasis_superset {s : Set A}
    (hs : AlgebraicIndepOn R id s) :
    ∃ t, s ⊆ t ∧ IsTranscendenceBasis R ((↑) : t → A) := by
  simpa [← isTranscendenceBasis_iff_maximal]
    using exists_maximal_algebraicIndependent s _ (subset_univ _) hs

variable (A)

theorem exists_isTranscendenceBasis [FaithfulSMul R A] :
    ∃ s : Set A, IsTranscendenceBasis R ((↑) : s → A) := by
  simpa using exists_isTranscendenceBasis_superset
    ((algebraicIndependent_empty_iff R A).mpr (FaithfulSMul.algebraMap_injective R A))

theorem exists_isTranscendenceBasis' [FaithfulSMul R A] :
    ∃ (ι : Type w) (x : ι → A), IsTranscendenceBasis R x :=
  have ⟨s, h⟩ := exists_isTranscendenceBasis R A
  ⟨s, Subtype.val, h⟩

variable {A}

open Cardinal in

theorem trdeg_eq_iSup_cardinalMk_isTranscendenceBasis :
    trdeg R A = ⨆ ι : { s : Set A // IsTranscendenceBasis R ((↑) : s → A) }, #ι.1 := by
  refine (ciSup_le' fun s ↦ ?_).antisymm
    (ciSup_le' fun s ↦ le_ciSup_of_le (bddAbove_range _) ⟨s, s.2.1⟩ le_rfl)
  choose t ht using exists_isTranscendenceBasis_superset s.2
  exact le_ciSup_of_le (bddAbove_range _) ⟨t, ht.2⟩ (mk_le_mk_of_subset ht.1)

variable {R}

theorem AlgebraicIndependent.isTranscendenceBasis_iff [Nontrivial R]
    (i : AlgebraicIndependent R x) :
    IsTranscendenceBasis R x ↔
      ∀ (κ : Type w) (w : κ → A) (_ : AlgebraicIndependent R w) (j : ι → κ) (_ : w ∘ j = x),
        Surjective j := by
  fconstructor
  · rintro p κ w i' j rfl
    have p := p.2 (range w) i'.coe_range (range_comp_subset_range _ _)
    rw [range_comp, ← @image_univ _ _ w] at p
    exact range_eq_univ.mp (image_injective.mpr i'.injective p)
  · intro p
    use i
    intro w i' h
    specialize p w ((↑) : w → A) i' (fun i => ⟨x i, range_subset_iff.mp h i⟩) (by ext; simp)
    have q := congr_arg (fun s => ((↑) : w → A) '' s) p.range_eq
    dsimp at q
    rw [← image_univ, image_image] at q
    simpa using q

theorem IsTranscendenceBasis.isAlgebraic [Nontrivial R] (hx : IsTranscendenceBasis R x) :
    Algebra.IsAlgebraic (adjoin R (range x)) A := by
  constructor
  intro a
  rw [← not_iff_comm.1 (hx.1.option_iff_transcendental _).symm]
  intro ai
  have h₁ : range x ⊆ range fun o : Option ι => o.elim a x := by
    rintro x ⟨y, rfl⟩
    exact ⟨some y, rfl⟩
  have h₂ : range x ≠ range fun o : Option ι => o.elim a x := by
    intro h
    have : a ∈ range x := by
      rw [h]
      exact ⟨none, rfl⟩
    rcases this with ⟨b, rfl⟩
    have : some b = none := ai.injective rfl
    simpa
  exact h₂ (hx.2 (Set.range fun o : Option ι => o.elim a x)
    ((algebraicIndependent_subtype_range ai.injective).2 ai) h₁)

theorem AlgebraicIndependent.isTranscendenceBasis_iff_isAlgebraic
    [Nontrivial R] (ind : AlgebraicIndependent R x) :
    IsTranscendenceBasis R x ↔ Algebra.IsAlgebraic (adjoin R (range x)) A := by
  refine ⟨(·.isAlgebraic), fun alg ↦ ⟨ind, fun s ind_s hxs ↦ of_not_not fun hxs' ↦ ?_⟩⟩
  have : ¬ s ⊆ range x := (hxs' <| hxs.antisymm ·)
  have ⟨a, has, hax⟩ := not_subset.mp this
  rw [show range x = Subtype.val '' range (Set.inclusion hxs) by
    rw [← range_comp, val_comp_inclusion, Subtype.range_val]] at alg
  refine ind_s.transcendental_adjoin (s := range (inclusion hxs)) (i := ⟨a, has⟩) ?_ (alg.1 _)
  simpa using hax

theorem isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic [Nontrivial R] :
    IsTranscendenceBasis R x ↔
      AlgebraicIndependent R x ∧ Algebra.IsAlgebraic (adjoin R (range x)) A :=
  ⟨fun h ↦ ⟨h.1, h.1.isTranscendenceBasis_iff_isAlgebraic.mp h⟩,
    fun ⟨ind, alg⟩ ↦ ind.isTranscendenceBasis_iff_isAlgebraic.mpr alg⟩

lemma IsTranscendenceBasis.algebraMap_comp
    [Nontrivial R] [NoZeroDivisors S] [Algebra.IsAlgebraic S A] [FaithfulSMul S A]
    {x : ι → S} (hx : IsTranscendenceBasis R x) : IsTranscendenceBasis R (algebraMap S A ∘ x) := by
  let f := IsScalarTower.toAlgHom R S A
  refine hx.1.map (f := f) (FaithfulSMul.algebraMap_injective S A).injOn
    |>.isTranscendenceBasis_iff_isAlgebraic.mpr ?_
  rw [Set.range_comp, ← AlgHom.map_adjoin]
  set Rx := adjoin R (range x)
  let e := Rx.equivMapOfInjective f (FaithfulSMul.algebraMap_injective S A)
  letI := e.toRingHom.toAlgebra
  haveI : IsScalarTower Rx (Rx.map f) A := .of_algebraMap_eq fun x ↦ rfl
  have : Algebra.IsAlgebraic Rx S := hx.isAlgebraic
  have : Algebra.IsAlgebraic Rx A := .trans _ S _
  exact .extendScalars e.injective

lemma IsTranscendenceBasis.isAlgebraic_iff [IsDomain S] [NoZeroDivisors A]
    {ι : Type*} {v : ι → A} (hv : IsTranscendenceBasis R v) :
    Algebra.IsAlgebraic S A ↔ ∀ i, IsAlgebraic S (v i) := by
  refine ⟨fun _ i ↦ Algebra.IsAlgebraic.isAlgebraic (v i), fun H ↦ ?_⟩
  let Rv := adjoin R (range v)
  let Sv := adjoin S (range v)
  have : Algebra.IsAlgebraic S Sv := by
    simpa [Sv, ← Subalgebra.isAlgebraic_iff, isAlgebraic_adjoin_iff]
  have le : Rv ≤ Sv.restrictScalars R := by
    rw [Subalgebra.restrictScalars_adjoin]; exact le_sup_right
  letI : Algebra Rv Sv := (Subalgebra.inclusion le).toAlgebra
  have : IsScalarTower Rv Sv A := .of_algebraMap_eq fun x ↦ rfl
  have := (algebraMap R S).domain_nontrivial
  have := hv.isAlgebraic
  have : Algebra.IsAlgebraic Sv A := .extendScalars (Subalgebra.inclusion_injective le)
  exact .trans _ Sv _

variable (ι R)

theorem IsTranscendenceBasis.mvPolynomial [Nontrivial R] :
    IsTranscendenceBasis R (X (R := R) (σ := ι)) := by
  refine isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic.2 ⟨algebraicIndependent_X .., ?_⟩
  rw [adjoin_range_X]
  set A := MvPolynomial ι R
  have := Algebra.isIntegral_of_surjective (R := (⊤ : Subalgebra R A)) (B := A) (⟨⟨·, ⟨⟩⟩, rfl⟩)
  infer_instance

theorem IsTranscendenceBasis.mvPolynomial' [Nonempty ι] :
    IsTranscendenceBasis R (X (R := R) (σ := ι)) := by nontriviality R; exact .mvPolynomial ι R

theorem IsTranscendenceBasis.polynomial [Nonempty ι] [Subsingleton ι] :
    IsTranscendenceBasis R fun _ : ι ↦ (.X : Polynomial R) := by
  nontriviality R
  have := (nonempty_unique ι).some
  refine (isTranscendenceBasis_equiv (Equiv.equivPUnit.{_, 1} _).symm).mp <|
    (MvPolynomial.pUnitAlgEquiv R).symm.isTranscendenceBasis_iff.mp ?_
  convert IsTranscendenceBasis.mvPolynomial PUnit R
  ext; simp

variable {ι R}

theorem IsTranscendenceBasis.sumElim_comp [NoZeroDivisors A] {x : ι → S} {y : ι' → A}
    (hx : IsTranscendenceBasis R x) (hy : IsTranscendenceBasis S y) :
    IsTranscendenceBasis R (Sum.elim y (algebraMap S A ∘ x)) := by
  cases subsingleton_or_nontrivial R
  · rw [isTranscendenceBasis_iff_of_subsingleton] at hx ⊢; infer_instance
  rw [(hx.1.sumElim_comp hy.1).isTranscendenceBasis_iff_isAlgebraic]
  set Rx := adjoin R (range x)
  let Rxy := adjoin Rx (range y)
  rw [show adjoin R (range <| Sum.elim y (algebraMap S A ∘ x)) = Rxy.restrictScalars R by
    rw [← adjoin_algebraMap_image_union_eq_adjoin_adjoin, Sum.elim_range, union_comm, range_comp]]
  change Algebra.IsAlgebraic Rxy A
  have := hx.1.algebraMap_injective.nontrivial
  have := hy.1.algebraMap_injective.nontrivial
  have := hy.isAlgebraic
  set Sy := adjoin S (range y)
  let _ : Algebra Rxy Sy := by
    refine (Subalgebra.inclusion (T := Sy.restrictScalars Rx) <| adjoin_le ?_).toAlgebra
    rintro _ ⟨i, rfl⟩; exact subset_adjoin (s := range y) ⟨i, rfl⟩
  have : IsScalarTower Rxy Sy A := .of_algebraMap_eq fun ⟨a, _⟩ ↦ show a = _ from rfl
  have : IsScalarTower Rx Rxy Sy := .of_algebraMap_eq fun ⟨a, _⟩ ↦ Subtype.ext rfl
  have : Algebra.IsAlgebraic Rxy Sy := by
    refine ⟨fun ⟨a, ha⟩ ↦ adjoin_induction ?_ (fun _ ↦ .extendScalars (R := Rx) ?_ ?_)
      (fun _ _ _ _ ↦ .add) (fun _ _ _ _ ↦ .mul) ha⟩
    · rintro _ ⟨i, rfl⟩; exact isAlgebraic_algebraMap (⟨y i, subset_adjoin ⟨i, rfl⟩⟩ : Rxy)
    · exact fun _ _ ↦ (Subtype.ext <| hy.1.algebraMap_injective <| Subtype.ext_iff.mp ·)
    · exact (hx.isAlgebraic.1 _).algHom (IsScalarTower.toAlgHom Rx S Sy)
  exact .trans _ Sy _

theorem IsTranscendenceBasis.isEmpty_iff_isAlgebraic [Nontrivial R]
    (hx : IsTranscendenceBasis R x) :
    IsEmpty ι ↔ Algebra.IsAlgebraic R A := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ hx.1.isEmpty_of_isAlgebraic⟩
  have := hx.isAlgebraic
  rw [Set.range_eq_empty x, adjoin_empty] at this
  exact algebra_isAlgebraic_of_algebra_isAlgebraic_bot_left R A

theorem IsTranscendenceBasis.nonempty_iff_transcendental [Nontrivial R]
    (hx : IsTranscendenceBasis R x) :
    Nonempty ι ↔ Algebra.Transcendental R A := by
  rw [← not_isEmpty_iff, Algebra.transcendental_iff_not_isAlgebraic, hx.isEmpty_iff_isAlgebraic]

theorem IsTranscendenceBasis.isAlgebraic_field {F E : Type*} {x : ι → E}
    [Field F] [Field E] [Algebra F E] (hx : IsTranscendenceBasis F x) :
    Algebra.IsAlgebraic (IntermediateField.adjoin F (range x)) E := by
  haveI := hx.isAlgebraic
  set S := range x
  letI : Algebra (adjoin F S) (IntermediateField.adjoin F S) :=
    (Subalgebra.inclusion (IntermediateField.algebra_adjoin_le_adjoin F S)).toRingHom.toAlgebra
  haveI : IsScalarTower (adjoin F S) (IntermediateField.adjoin F S) E :=
    IsScalarTower.of_algebraMap_eq (congrFun rfl)
  exact Algebra.IsAlgebraic.extendScalars (R := adjoin F S) (Subalgebra.inclusion_injective _)

namespace AlgebraicIndependent

variable (R A) [FaithfulSMul R A]

variable [NoZeroDivisors A]

set_option backward.privateInPublic true in

private def indepMatroid : IndepMatroid A where
  E := univ
  Indep := AlgebraicIndepOn R id
  indep_empty := (algebraicIndependent_empty_iff ..).mpr (FaithfulSMul.algebraMap_injective R A)
  indep_subset _ _ := (·.mono)
  indep_aug I B I_ind h B_base := by
    contrapose! h
    rw [← isTranscendenceBasis_iff_maximal] at B_base ⊢
    cases subsingleton_or_nontrivial R
    · rw [isTranscendenceBasis_iff_of_subsingleton] at B_base ⊢
      by_contra this
      have ⟨b, hb⟩ := B_base
      exact h b ⟨hb, fun hbI ↦ this ⟨b, hbI⟩⟩ .of_subsingleton
    apply I_ind.isTranscendenceBasis_iff_isAlgebraic.mpr
    replace B_base := B_base.isAlgebraic
    simp_rw +instances [id_eq]
    rw [Subtype.range_val] at B_base ⊢
    refine ⟨fun a ↦ (B_base.1 a).adjoin_of_forall_isAlgebraic fun x hx ↦ ?_⟩
    contrapose! h
    exact ⟨x, hx, I_ind.insert <| by rwa [image_id]⟩
  indep_maximal X _ I ind hIX := exists_maximal_algebraicIndependent I X hIX ind
  subset_ground _ _ := subset_univ _

set_option backward.privateInPublic true in

set_option backward.privateInPublic.warn false in

def matroid : Matroid A := (indepMatroid R A).matroid.copyBase univ
  (fun s ↦ IsTranscendenceBasis R ((↑) : s → A)) rfl
  (fun B ↦ by simp_rw [Matroid.isBase_iff_maximal_indep, isTranscendenceBasis_iff_maximal]; rfl)

-- INSTANCE (free from Core): :
