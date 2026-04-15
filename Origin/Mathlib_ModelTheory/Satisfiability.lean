/-
Extracted from ModelTheory/Satisfiability.lean
Genuine: 19 of 20 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# First-Order Satisfiability

This file deals with the satisfiability of first-order theories, as well as equivalence over them.

## Main Definitions

- `FirstOrder.Language.Theory.IsSatisfiable`: `T.IsSatisfiable` indicates that `T` has a nonempty
  model.
- `FirstOrder.Language.Theory.IsFinitelySatisfiable`: `T.IsFinitelySatisfiable` indicates that
  every finite subset of `T` is satisfiable.
- `FirstOrder.Language.Theory.IsComplete`: `T.IsComplete` indicates that `T` is satisfiable and
  models each sentence or its negation.
- `Cardinal.Categorical`: A theory is `κ`-categorical if all models of size `κ` are isomorphic.

## Main Results

- The Compactness Theorem, `FirstOrder.Language.Theory.isSatisfiable_iff_isFinitelySatisfiable`,
  shows that a theory is satisfiable iff it is finitely satisfiable.
- `FirstOrder.Language.completeTheory.isComplete`: The complete theory of a structure is
  complete.
- `FirstOrder.Language.Theory.exists_large_model_of_infinite_model` shows that any theory with an
  infinite model has arbitrarily large models.
- `FirstOrder.Language.Theory.exists_elementaryEmbedding_card_eq`: The Upward Löwenheim–Skolem
  Theorem: If `κ` is a cardinal greater than the cardinalities of `L` and an infinite `L`-structure
  `M`, then `M` has an elementary extension of cardinality `κ`.

## Implementation Details

- Satisfiability of an `L.Theory` `T` is defined in the minimal universe containing all the symbols
  of `L`. By Löwenheim-Skolem, this is equivalent to satisfiability in any universe.
-/

universe u v w w'

open Cardinal CategoryTheory

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {T : L.Theory} {α : Type w} {n : ℕ}

namespace Theory

variable (T)

def IsSatisfiable : Prop :=
  Nonempty (ModelType.{u, v, max u v} T)

def IsFinitelySatisfiable : Prop :=
  ∀ T0 : Finset L.Sentence, (T0 : L.Theory) ⊆ T → IsSatisfiable (T0 : L.Theory)

variable {T} {T' : L.Theory}

theorem Model.isSatisfiable (M : Type w) [Nonempty M] [L.Structure M] [M ⊨ T] :
    T.IsSatisfiable :=
  ⟨((⊥ : Substructure _ (ModelType.of T M)).elementarySkolem₁Reduct.toModel T).shrink⟩

theorem IsSatisfiable.mono (h : T'.IsSatisfiable) (hs : T ⊆ T') : T.IsSatisfiable :=
  ⟨(Theory.Model.mono (ModelType.is_model h.some) hs).bundled⟩

theorem isSatisfiable_empty (L : Language.{u, v}) : IsSatisfiable (∅ : L.Theory) :=
  ⟨default⟩

theorem isSatisfiable_of_isSatisfiable_onTheory {L' : Language.{w, w'}} (φ : L →ᴸ L')
    (h : (φ.onTheory T).IsSatisfiable) : T.IsSatisfiable :=
  Model.isSatisfiable (h.some.reduct φ)

theorem isSatisfiable_onTheory_iff {L' : Language.{w, w'}} {φ : L →ᴸ L'} (h : φ.Injective) :
    (φ.onTheory T).IsSatisfiable ↔ T.IsSatisfiable := by
  classical
    refine ⟨isSatisfiable_of_isSatisfiable_onTheory φ, fun h' => ?_⟩
    haveI : Inhabited h'.some := Classical.inhabited_of_nonempty'
    exact Model.isSatisfiable (h'.some.defaultExpansion h)

theorem IsSatisfiable.isFinitelySatisfiable (h : T.IsSatisfiable) : T.IsFinitelySatisfiable :=
  fun _ => h.mono

theorem isSatisfiable_iff_isFinitelySatisfiable {T : L.Theory} :
    T.IsSatisfiable ↔ T.IsFinitelySatisfiable :=
  ⟨Theory.IsSatisfiable.isFinitelySatisfiable, fun h => by
    classical
      set M : Finset T → Type max u v := fun T0 : Finset T =>
        (h (T0.map (Function.Embedding.subtype fun x => x ∈ T)) T0.map_subtype_subset).some.Carrier
      let M' := Filter.Product (Ultrafilter.of (Filter.atTop : Filter (Finset T))) M
      have h' : M' ⊨ T := by
        refine ⟨fun φ hφ => ?_⟩
        rw [Ultraproduct.sentence_realize]
        refine
          Filter.Eventually.filter_mono (Ultrafilter.of_le _)
            (Filter.eventually_atTop.2
              ⟨{⟨φ, hφ⟩}, fun s h' =>
                Theory.realize_sentence_of_mem (s.map (Function.Embedding.subtype fun x => x ∈ T))
                  ?_⟩)
        simp only [Finset.coe_map, Function.Embedding.coe_subtype, Set.mem_image, Finset.mem_coe,
          Subtype.exists, exists_and_right, exists_eq_right]
        exact ⟨hφ, h' (Finset.mem_singleton_self _)⟩
      exact ⟨ModelType.of T M'⟩⟩

theorem isSatisfiable_union_distinctConstantsTheory_of_card_le (T : L.Theory) (s : Set α)
    (M : Type w') [Nonempty M] [L.Structure M] [M ⊨ T]
    (h : Cardinal.lift.{w'} #s ≤ Cardinal.lift.{w} #M) :
    ((L.lhomWithConstants α).onTheory T ∪ L.distinctConstantsTheory s).IsSatisfiable := by
  haveI : Inhabited M := Classical.inhabited_of_nonempty inferInstance
  rw [Cardinal.lift_mk_le'] at h
  letI : (constantsOn α).Structure M := constantsOn.structure (Function.extend (↑) h.some default)
  have : M ⊨ (L.lhomWithConstants α).onTheory T ∪ L.distinctConstantsTheory s := by
    refine ((LHom.onTheory_model _ _).2 inferInstance).union ?_
    rw [model_distinctConstantsTheory]
    refine fun a as b bs ab => ?_
    rw [← Subtype.coe_mk a as, ← Subtype.coe_mk b bs, ← Subtype.ext_iff]
    exact
      h.some.injective
        ((Subtype.coe_injective.extend_apply h.some default ⟨a, as⟩).symm.trans
          (ab.trans (Subtype.coe_injective.extend_apply h.some default ⟨b, bs⟩)))
  exact Model.isSatisfiable M

theorem isSatisfiable_union_distinctConstantsTheory_of_infinite (T : L.Theory) (s : Set α)
    (M : Type w') [L.Structure M] [M ⊨ T] [Infinite M] :
    ((L.lhomWithConstants α).onTheory T ∪ L.distinctConstantsTheory s).IsSatisfiable := by
  classical
    rw [distinctConstantsTheory_eq_iUnion, Set.union_iUnion, isSatisfiable_directed_union_iff]
    · exact fun t =>
        isSatisfiable_union_distinctConstantsTheory_of_card_le T _ M
          ((lift_le_aleph0.2 (finset_card_lt_aleph0 _).le).trans
            (aleph0_le_lift.2 (aleph0_le_mk M)))
    · apply Monotone.directed_le
      refine monotone_const.union (monotone_distinctConstantsTheory.comp ?_)
      simp only [Finset.coe_map, Function.Embedding.coe_subtype]
      exact Monotone.comp (g := Set.image ((↑) : s → α)) (f := ((↑) : Finset s → Set s))
        Set.monotone_image fun _ _ => Finset.coe_subset.2

theorem exists_large_model_of_infinite_model (T : L.Theory) (κ : Cardinal.{w}) (M : Type w')
    [L.Structure M] [M ⊨ T] [Infinite M] :
    ∃ N : ModelType.{_, _, max u v w} T, Cardinal.lift.{max u v w} κ ≤ #N := by
  obtain ⟨N⟩ :=
    isSatisfiable_union_distinctConstantsTheory_of_infinite T (Set.univ : Set κ.out) M
  refine ⟨(N.is_model.mono Set.subset_union_left).bundled.reduct _, ?_⟩
  haveI : N ⊨ distinctConstantsTheory _ _ := N.is_model.mono Set.subset_union_right
  rw [ModelType.reduct_Carrier, coe_of]
  refine _root_.trans (lift_le.2 (le_of_eq (Cardinal.mk_out κ).symm)) ?_
  rw [← mk_univ]
  refine
    (card_le_of_model_distinctConstantsTheory L Set.univ N).trans (lift_le.{max u v w}.1 ?_)
  rw [lift_lift]

theorem isSatisfiable_iUnion_iff_isSatisfiable_iUnion_finset {ι : Type*} (T : ι → L.Theory) :
    IsSatisfiable (⋃ i, T i) ↔ ∀ s : Finset ι, IsSatisfiable (⋃ i ∈ s, T i) := by
  classical
    refine
      ⟨fun h s => h.mono (Set.iUnion_mono fun _ => Set.iUnion_subset_iff.2 fun _ => refl _),
        fun h => ?_⟩
    rw [isSatisfiable_iff_isFinitelySatisfiable]
    intro s hs
    rw [Set.iUnion_eq_iUnion_finset] at hs
    obtain ⟨t, ht⟩ := Directed.exists_mem_subset_of_finset_subset_biUnion (by
      exact Monotone.directed_le fun t1 t2 (h : ∀ ⦃x⦄, x ∈ t1 → x ∈ t2) =>
        Set.iUnion_mono fun _ => Set.iUnion_mono' fun h1 => ⟨h h1, refl _⟩) hs
    exact (h t).mono ht

end Theory

variable (L)

theorem exists_elementaryEmbedding_card_eq_of_le (M : Type w') [L.Structure M] [Nonempty M]
    (κ : Cardinal.{w}) (h1 : ℵ₀ ≤ κ) (h2 : lift.{w} L.card ≤ Cardinal.lift.{max u v} κ)
    (h3 : lift.{w'} κ ≤ Cardinal.lift.{w} #M) :
    ∃ N : Bundled L.Structure, Nonempty (N ↪ₑ[L] M) ∧ #N = κ := by
  obtain ⟨S, _, hS⟩ := exists_elementarySubstructure_card_eq L ∅ κ h1 (by simp) h2 h3
  have : Small.{w} S := by
    rw [← lift_inj.{_, w + 1}, lift_lift, lift_lift] at hS
    exact small_iff_lift_mk_lt_univ.2 (lt_of_eq_of_lt hS κ.lift_lt_univ')
  refine
    ⟨(equivShrink S).bundledInduced L,
      ⟨S.subtype.comp (Equiv.bundledInducedEquiv L _).symm.toElementaryEmbedding⟩,
      lift_inj.1 (_root_.trans ?_ hS)⟩
  simp only [Equiv.bundledInduced_α, lift_mk_shrink']

theorem exists_elementaryEmbedding_card_eq_of_ge (M : Type w') [L.Structure M] [iM : Infinite M]
    (κ : Cardinal.{w}) (h1 : Cardinal.lift.{w} L.card ≤ Cardinal.lift.{max u v} κ)
    (h2 : Cardinal.lift.{w} #M ≤ Cardinal.lift.{w'} κ) :
    ∃ N : Bundled L.Structure, Nonempty (M ↪ₑ[L] N) ∧ #N = κ := by
  obtain ⟨N0, hN0⟩ := (L.elementaryDiagram M).exists_large_model_of_infinite_model κ M
  rw [← lift_le.{max u v}, lift_lift, lift_lift] at h2
  obtain ⟨N, ⟨NN0⟩, hN⟩ :=
    exists_elementaryEmbedding_card_eq_of_le L[[M]] N0 κ
      (aleph0_le_lift.1 ((aleph0_le_lift.2 (aleph0_le_mk M)).trans h2))
      (by
        simp only [card_withConstants, lift_add, lift_lift]
        rw [add_comm, add_eq_max (aleph0_le_lift.2 (infinite_iff.1 iM)), max_le_iff]
        rw [← lift_le.{w'}, lift_lift, lift_lift] at h1
        exact ⟨h2, h1⟩)
      (hN0.trans (by rw [← lift_umax, lift_id]))
  letI := (lhomWithConstants L M).reduct N
  haveI h : N ⊨ L.elementaryDiagram M :=
    (NN0.theory_model_iff (L.elementaryDiagram M)).2 inferInstance
  refine ⟨Bundled.of N, ⟨?_⟩, hN⟩
  apply ElementaryEmbedding.ofModelsElementaryDiagram L M N

end

theorem exists_elementaryEmbedding_card_eq (M : Type w') [L.Structure M] [iM : Infinite M]
    (κ : Cardinal.{w}) (h1 : ℵ₀ ≤ κ) (h2 : lift.{w} L.card ≤ Cardinal.lift.{max u v} κ) :
    ∃ N : Bundled L.Structure, (Nonempty (N ↪ₑ[L] M) ∨ Nonempty (M ↪ₑ[L] N)) ∧ #N = κ := by
  cases le_or_gt (lift.{w'} κ) (Cardinal.lift.{w} #M) with
  | inl h =>
    obtain ⟨N, hN1, hN2⟩ := exists_elementaryEmbedding_card_eq_of_le L M κ h1 h2 h
    exact ⟨N, Or.inl hN1, hN2⟩
  | inr h =>
    obtain ⟨N, hN1, hN2⟩ := exists_elementaryEmbedding_card_eq_of_ge L M κ h2 (le_of_lt h)
    exact ⟨N, Or.inr hN1, hN2⟩

theorem exists_elementarilyEquivalent_card_eq (M : Type w') [L.Structure M] [Infinite M]
    (κ : Cardinal.{w}) (h1 : ℵ₀ ≤ κ) (h2 : lift.{w} L.card ≤ Cardinal.lift.{max u v} κ) :
    ∃ N : CategoryTheory.Bundled L.Structure, (M ≅[L] N) ∧ #N = κ := by
  obtain ⟨N, NM | MN, hNκ⟩ := exists_elementaryEmbedding_card_eq L M κ h1 h2
  · exact ⟨N, NM.some.elementarilyEquivalent.symm, hNκ⟩
  · exact ⟨N, MN.some.elementarilyEquivalent, hNκ⟩

variable {L}

namespace Theory

theorem exists_model_card_eq (h : ∃ M : ModelType.{u, v, max u v} T, Infinite M) (κ : Cardinal.{w})
    (h1 : ℵ₀ ≤ κ) (h2 : Cardinal.lift.{w} L.card ≤ Cardinal.lift.{max u v} κ) :
    ∃ N : ModelType.{u, v, w} T, #N = κ := by
  cases h with
  | intro M MI =>
    obtain ⟨N, hN, rfl⟩ := exists_elementarilyEquivalent_card_eq L M κ h1 h2
    haveI : Nonempty N := hN.nonempty
    exact ⟨hN.theory_model.bundled, rfl⟩

variable (T)

def ModelsBoundedFormula (φ : L.BoundedFormula α n) : Prop :=
  ∀ (M : ModelType.{u, v, max u v w} T) (v : α → M) (xs : Fin n → M), φ.Realize v xs
