/-
Extracted from LinearAlgebra/Dimension/OrzechProperty.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Bases of modules and the Orzech property

It is shown in this file that any spanning set of a module over a ring satisfying the Orzech
property of cardinality not exceeding the rank of the module must be linearly independent,
and therefore is a basis.
-/

section Basis

open Module Submodule

variable {R M : Type*} [Semiring R] [OrzechProperty R] [AddCommMonoid M] [Module R M]

theorem linearIndependent_of_top_le_span_of_card_le_finrank {ι : Type*} [Fintype ι] {b : ι → M}
    (spans : ⊤ ≤ span R (Set.range b)) (card_le : Fintype.card ι ≤ finrank R M) :
    LinearIndependent R b := by
  rw [← Finsupp.range_linearCombination, top_le_iff, LinearMap.range_eq_top] at spans
  have := Module.Finite.of_surjective _ spans
  have ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank card_le
  exact OrzechProperty.injective_of_surjective_of_injective
    _ _ (hf.comp _ (Fintype.equivFin _).injective) spans

theorem linearIndependent_of_top_le_span_of_card_eq_finrank {ι : Type*} [Fintype ι] {b : ι → M}
    (spans : ⊤ ≤ span R (Set.range b)) (card_eq : Fintype.card ι = finrank R M) :
    LinearIndependent R b :=
  linearIndependent_of_top_le_span_of_card_le_finrank spans card_eq.le

theorem linearIndependent_iff_card_eq_finrank_span [Nontrivial R] {ι} [Fintype ι] {b : ι → M} :
    LinearIndependent R b ↔ Fintype.card ι = (Set.range b).finrank R where
  mp h := (finrank_span_eq_card h).symm
  mpr hc := by
    refine (LinearMap.linearIndependent_iff_of_injOn _ (subtype_injective _).injOn).mpr <|
      linearIndependent_of_top_le_span_of_card_eq_finrank (b := fun i ↦ ⟨b i, subset_span ⟨i, rfl⟩⟩)
        (fun ⟨_, _⟩ _ ↦ (subtype_injective _).mem_set_image.mp ?_) hc
    rwa [← map_coe, ← span_image, ← Set.range_comp]

theorem linearIndependent_iff_card_le_finrank_span [Nontrivial R] {ι} [Fintype ι] {b : ι → M} :
    LinearIndependent R b ↔ Fintype.card ι ≤ (Set.range b).finrank R := by
  rw [linearIndependent_iff_card_eq_finrank_span, (finrank_range_le_card _).ge_iff_eq']

noncomputable def basisOfTopLeSpanOfCardEqFinrank {ι : Type*} [Fintype ι] (b : ι → M)
    (le_span : ⊤ ≤ span R (Set.range b)) (card_eq : Fintype.card ι = finrank R M) : Basis ι R M :=
  Basis.mk (linearIndependent_of_top_le_span_of_card_eq_finrank le_span card_eq) le_span
