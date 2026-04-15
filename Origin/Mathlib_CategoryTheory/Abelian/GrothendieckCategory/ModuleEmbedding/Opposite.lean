/-
Extracted from CategoryTheory/Abelian/GrothendieckCategory/ModuleEmbedding/Opposite.lean
Genuine: 7 of 14 | Dissolved: 0 | Infrastructure: 7
-/
import Origin.Core

/-!
# Embedding opposites of Grothendieck categories

If `C` is Grothendieck abelian and `F : D ⥤ Cᵒᵖ` is a functor from a small category, we construct
an object `G : Cᵒᵖ` such that `preadditiveCoyonedaObj G : Cᵒᵖ ⥤ ModuleCat (End G)ᵐᵒᵖ` is faithful
and exact and its precomposition with `F` is full if `F` is.
-/

universe v u

open CategoryTheory Limits Opposite ZeroObject

namespace CategoryTheory.Abelian.IsGrothendieckAbelian

variable {C : Type u} [Category.{v} C] {D : Type v} [SmallCategory D] (F : D ⥤ Cᵒᵖ)

namespace OppositeModuleEmbedding

variable [Abelian C] [IsGrothendieckAbelian.{v} C]

variable (C) in

private noncomputable def projectiveSeparator : Cᵒᵖ :=
  (has_projective_separator (coseparator Cᵒᵖ) (isCoseparator_coseparator Cᵒᵖ)).choose

-- INSTANCE (free from Core): :

private theorem isSeparator_projectiveSeparator : IsSeparator (projectiveSeparator C) :=
  (has_projective_separator (coseparator Cᵒᵖ) (isCoseparator_coseparator Cᵒᵖ)).choose_spec.2

set_option backward.privateInPublic true in

private noncomputable def generator : Cᵒᵖ :=
  ∐ (fun (X : D) => ∐ fun (_ : projectiveSeparator C ⟶ F.obj X) => projectiveSeparator C)

set_option backward.isDefEq.respectTransparency false in

private theorem exists_epi (X : D) : ∃ f : generator F ⟶ F.obj X, Epi f := by
  classical
  refine ⟨Sigma.desc (Pi.single X (𝟙 _)) ≫ Sigma.desc (fun f => f), ?_⟩
  have h := (isSeparator_iff_epi (projectiveSeparator C)).1
    isSeparator_projectiveSeparator (F.obj X)
  suffices Epi (Sigma.desc (Pi.single X (𝟙 _))) from epi_comp' this h
  exact SplitEpi.epi ⟨Sigma.ι (fun (X : D) => ∐ fun _ => projectiveSeparator C) X, by simp⟩

-- INSTANCE (free from Core): :

private theorem isSeparator [Nonempty D] : IsSeparator (generator F) := by
  apply isSeparator_sigma_of_isSeparator _ Classical.ofNonempty
  apply isSeparator_sigma_of_isSeparator _ 0
  exact isSeparator_projectiveSeparator

set_option backward.privateInPublic true in

set_option backward.privateInPublic.warn false in

def EmbeddingRing : Type v := (End (generator F))ᵐᵒᵖ

set_option backward.privateInPublic true in

set_option backward.privateInPublic.warn false in

-- INSTANCE (free from Core): :

set_option backward.privateInPublic true in

set_option backward.privateInPublic.warn false in

noncomputable def embedding : Cᵒᵖ ⥤ ModuleCat.{v} (EmbeddingRing F) :=
  preadditiveCoyonedaObj (generator F)

-- INSTANCE (free from Core): faithful_embedding

-- INSTANCE (free from Core): full_embedding

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): preservesFiniteLimits_embedding

-- INSTANCE (free from Core): preservesFiniteColimits_embedding

end OppositeModuleEmbedding

end CategoryTheory.Abelian.IsGrothendieckAbelian
