/-
Extracted from CategoryTheory/Sites/Coherent/SheafComparison.lean
Genuine: 13 of 18 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-!

# Categories of coherent sheaves

Given a fully faithful functor `F : C ⥤ D` into a precoherent category, which preserves and reflects
finite effective epi families, and satisfies the property `F.EffectivelyEnough` (meaning that to
every object in `C` there is an effective epi from an object in the image of `F`), the categories
of coherent sheaves on `C` and `D` are equivalent (see
`CategoryTheory.coherentTopology.equivalence`).

The main application of this equivalence is the characterisation of condensed sets as coherent
sheaves on either `CompHaus`, `Profinite` or `Stonean`. See the file
`Mathlib/Condensed/Equivalence.lean`.

We give the corresponding result for the regular topology as well (see
`CategoryTheory.regularTopology.equivalence`).
-/

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

open Limits Functor regularTopology

variable {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)

namespace coherentTopology

variable [F.PreservesFiniteEffectiveEpiFamilies] [F.ReflectsFiniteEffectiveEpiFamilies]
  [F.Full] [F.Faithful] [F.EffectivelyEnough] [Precoherent D]

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): :

set_option backward.isDefEq.respectTransparency false in

theorem exists_effectiveEpiFamily_iff_mem_induced (X : C) (S : Sieve X) :
    (∃ (α : Type) (_ : Finite α) (Y : α → C) (π : (a : α) → (Y a ⟶ X)),
      EffectiveEpiFamily Y π ∧ (∀ a : α, (S.arrows) (π a))) ↔
    (S ∈ F.inducedTopology (coherentTopology _) X) := by
  refine ⟨fun ⟨α, _, Y, π, ⟨H₁, H₂⟩⟩ ↦ ?_, fun hS ↦ ?_⟩
  · apply (mem_sieves_iff_hasEffectiveEpiFamily (Sieve.functorPushforward _ S)).mpr
    refine ⟨α, inferInstance, fun i => F.obj (Y i),
      fun i => F.map (π i), ⟨?_,
      fun a => Sieve.image_mem_functorPushforward F S (H₂ a)⟩⟩
    exact F.map_finite_effectiveEpiFamily _ _
  · obtain ⟨α, _, Y, π, ⟨H₁, H₂⟩⟩ := (mem_sieves_iff_hasEffectiveEpiFamily _).mp hS
    refine ⟨α, inferInstance, ?_⟩
    let Z : α → C := fun a ↦ (Functor.EffectivelyEnough.presentation (F := F) (Y a)).some.p
    let g₀ : (a : α) → F.obj (Z a) ⟶ Y a := fun a ↦ F.effectiveEpiOver (Y a)
    have : EffectiveEpiFamily _ (fun a ↦ g₀ a ≫ π a) := inferInstance
    refine ⟨Z, fun a ↦ F.preimage (g₀ a ≫ π a), ?_, fun a ↦ (?_ : S.arrows (F.preimage _))⟩
    · refine F.finite_effectiveEpiFamily_of_map _ _ ?_
      simpa using this
    · obtain ⟨W, g₁, g₂, h₁, h₂⟩ := H₂ a
      rw [h₂]
      convert S.downward_closed h₁ (F.preimage (g₀ a ≫ g₂))
      exact F.map_injective (by simp)

lemma eq_induced : haveI := F.reflects_precoherent
    coherentTopology C =
      F.inducedTopology (coherentTopology _) := by
  ext X S
  have := F.reflects_precoherent
  rw [← exists_effectiveEpiFamily_iff_mem_induced F X]
  rw [← coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily S]

-- INSTANCE (free from Core): :

lemma coverPreserving : haveI := F.reflects_precoherent
    CoverPreserving (coherentTopology _) (coherentTopology _) F :=
  IsDenseSubsite.coverPreserving _ _ _

section SheafEquiv

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] (F : C ⥤ D)
  [F.PreservesFiniteEffectiveEpiFamilies] [F.ReflectsFiniteEffectiveEpiFamilies]
  [F.Full] [F.Faithful]
  [Precoherent D]
  [F.EffectivelyEnough]

noncomputable

def equivalence (A : Type u₃) [Category.{v₃} A] [∀ X, HasLimitsOfShape (StructuredArrow X F.op) A] :
    haveI := F.reflects_precoherent
    Sheaf (coherentTopology C) A ≌ Sheaf (coherentTopology D) A :=
  Functor.IsDenseSubsite.sheafEquiv _ _ F _

end SheafEquiv

section RegularExtensive

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] (F : C ⥤ D)
  [F.PreservesEffectiveEpis] [F.ReflectsEffectiveEpis]
  [F.Full] [F.Faithful]
  [FinitaryExtensive D] [Preregular D]
  [FinitaryPreExtensive C]
  [PreservesFiniteCoproducts F]
  [F.EffectivelyEnough]

noncomputable

def equivalence' (A : Type u₃) [Category.{v₃} A]
    [∀ X, HasLimitsOfShape (StructuredArrow X F.op) A] :
    haveI := F.reflects_precoherent
    Sheaf (coherentTopology C) A ≌ Sheaf (coherentTopology D) A :=
  Functor.IsDenseSubsite.sheafEquiv _ _ F _

end RegularExtensive

end coherentTopology

namespace regularTopology

variable [F.PreservesEffectiveEpis] [F.ReflectsEffectiveEpis] [F.Full] [F.Faithful]
  [F.EffectivelyEnough] [Preregular D]

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): :

set_option backward.isDefEq.respectTransparency false in

theorem exists_effectiveEpi_iff_mem_induced (X : C) (S : Sieve X) :
    (∃ (Y : C) (π : Y ⟶ X),
      EffectiveEpi π ∧ S.arrows π) ↔
    (S ∈ F.inducedTopology (regularTopology _) X) := by
  refine ⟨fun ⟨Y, π, ⟨H₁, H₂⟩⟩ ↦ ?_, fun hS ↦ ?_⟩
  · apply (mem_sieves_iff_hasEffectiveEpi (Sieve.functorPushforward _ S)).mpr
    refine ⟨F.obj Y, F.map π, ⟨?_, Sieve.image_mem_functorPushforward F S H₂⟩⟩
    exact F.map_effectiveEpi _
  · obtain ⟨Y, π, ⟨H₁, H₂⟩⟩ := (mem_sieves_iff_hasEffectiveEpi _).mp hS
    let g₀ := F.effectiveEpiOver Y
    refine ⟨_, F.preimage (g₀ ≫ π), ?_, (?_ : S.arrows (F.preimage _))⟩
    · refine F.effectiveEpi_of_map _ ?_
      simp only [map_preimage]
      infer_instance
    · obtain ⟨W, g₁, g₂, h₁, h₂⟩ := H₂
      rw [h₂]
      convert S.downward_closed h₁ (F.preimage (g₀ ≫ g₂))
      exact F.map_injective (by simp)

lemma eq_induced : haveI := F.reflects_preregular
    regularTopology C =
      F.inducedTopology (regularTopology _) := by
  ext X S
  have := F.reflects_preregular
  rw [← exists_effectiveEpi_iff_mem_induced F X]
  rw [← mem_sieves_iff_hasEffectiveEpi S]

-- INSTANCE (free from Core): :

lemma coverPreserving : haveI := F.reflects_preregular
    CoverPreserving (regularTopology _) (regularTopology _) F :=
  IsDenseSubsite.coverPreserving _ _ _

section SheafEquiv

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] (F : C ⥤ D)
  [F.PreservesEffectiveEpis] [F.ReflectsEffectiveEpis]
  [F.Full] [F.Faithful]
  [Preregular D]
  [F.EffectivelyEnough]

noncomputable

def equivalence (A : Type u₃) [Category.{v₃} A] [∀ X, HasLimitsOfShape (StructuredArrow X F.op) A] :
    haveI := F.reflects_preregular
    Sheaf (regularTopology C) A ≌ Sheaf (regularTopology D) A :=
  Functor.IsDenseSubsite.sheafEquiv _ _ F _

end SheafEquiv

end regularTopology

namespace Presheaf

variable {A : Type u₃} [Category.{v₃} A] (F : Cᵒᵖ ⥤ A)

theorem isSheaf_coherent_iff_regular_and_extensive [Preregular C] [FinitaryPreExtensive C] :
    IsSheaf (coherentTopology C) F ↔
    IsSheaf (extensiveTopology C) F ∧ IsSheaf (regularTopology C) F := by
  rw [← extensive_regular_generate_coherent]
  exact isSheaf_sup (extensiveCoverage C) (regularCoverage C) F

theorem isSheaf_iff_preservesFiniteProducts_and_equalizerCondition
    [Preregular C] [FinitaryExtensive C]
    [h : ∀ {Y X : C} (f : Y ⟶ X) [EffectiveEpi f], HasPullback f f] :
    IsSheaf (coherentTopology C) F ↔ PreservesFiniteProducts F ∧
      EqualizerCondition F := by
  rw [isSheaf_coherent_iff_regular_and_extensive]
  exact and_congr (isSheaf_iff_preservesFiniteProducts _)
    (@equalizerCondition_iff_isSheaf _ _ _ _ F _ h).symm

-- INSTANCE (free from Core): [Preregular

theorem isSheaf_iff_preservesFiniteProducts_of_projective [Preregular C] [FinitaryExtensive C]
    [∀ (X : C), Projective X] :
    IsSheaf (coherentTopology C) F ↔ PreservesFiniteProducts F := by
  rw [isSheaf_coherent_iff_regular_and_extensive, and_iff_left (isSheaf_of_projective F),
    isSheaf_iff_preservesFiniteProducts]

theorem isSheaf_iff_extensiveSheaf_of_projective [Preregular C] [FinitaryExtensive C]
    [∀ (X : C), Projective X] :
    IsSheaf (coherentTopology C) F ↔ IsSheaf (extensiveTopology C) F := by
  rw [isSheaf_iff_preservesFiniteProducts_of_projective, isSheaf_iff_preservesFiniteProducts]
