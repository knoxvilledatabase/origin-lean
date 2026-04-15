/-
Extracted from AlgebraicGeometry/Morphisms/OpenImmersion.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Open immersions

A morphism is an open immersion if the underlying map of spaces is an open embedding
`f : X ⟶ U ⊆ Y`, and the sheaf map `Y(V) ⟶ f _* X(V)` is an iso for each `V ⊆ U`.

Most of the theories are developed in `AlgebraicGeometry/OpenImmersion`, and we provide the
remaining theorems analogous to other lemmas in `AlgebraicGeometry/Morphisms/*`.

-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Topology

universe u

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in

lemma isOpenImmersion_SpecMap_iff_of_surjective {R S : CommRingCat}
    (f : R ⟶ S) (hf : Function.Surjective f.hom) :
    IsOpenImmersion (Spec.map f) ↔
    ∃ e, IsIdempotentElem e ∧ RingHom.ker f.hom = Ideal.span {e} := by
  constructor
  · intro H
    obtain ⟨e, he, he'⟩ := PrimeSpectrum.isClopen_iff_zeroLocus.mp
      ⟨PrimeSpectrum.isClosed_range_comap_of_surjective _ _ hf,
        (Spec.map f).isOpenEmbedding.isOpen_range⟩
    refine ⟨e, he, ?_⟩
    let φ : R ⟶ _ := (CommRingCat.ofHom (Ideal.Quotient.mk (.span {e})))
    have : IsOpenImmersion (Spec.map φ) :=
      have : IsLocalization.Away (1 - e) (↑R ⧸ Ideal.span {e}) :=
        IsLocalization.away_of_isIdempotentElem he.one_sub (by simp) Ideal.Quotient.mk_surjective
      IsOpenImmersion.of_isLocalization (1 - e)
    have H : Set.range (Spec.map φ) = Set.range (Spec.map f) :=
      ((range_comap_of_surjective _ _
        Ideal.Quotient.mk_surjective).trans (by simp)).trans he'.symm
    let i : S ≅ .of _ := (Scheme.Spec.preimageIso
      (IsOpenImmersion.isoOfRangeEq (Spec.map φ) (Spec.map f) H)).unop
    have hi : Function.Injective i.inv.hom := (ConcreteCategory.bijective_of_isIso i.inv).1
    have : f = φ ≫ i.inv := by apply Spec.map_injective; simp [i, ← Scheme.Spec_map]
    rw [this, CommRingCat.hom_comp, RingHom.ker_eq_comap_bot, ← Ideal.comap_comap,
      ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot i.inv.hom).mp hi,
      ← RingHom.ker_eq_comap_bot]
    simp [φ]
  · rintro ⟨e, he, he'⟩
    letI := f.hom.toAlgebra
    have : IsLocalization.Away (1 - e) S :=
      IsLocalization.away_of_isIdempotentElem he.one_sub (by simpa using he') hf
    exact IsOpenImmersion.of_isLocalization (1 - e)

variable {X Y : Scheme.{u}}
