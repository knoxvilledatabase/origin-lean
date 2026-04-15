/-
Extracted from CategoryTheory/Sites/EpiMono.lean
Genuine: 4 of 9 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-!
# Morphisms of sheaves factor as a locally surjective followed by a locally injective morphism

When morphisms in a concrete category `A` factor in a functorial manner as a surjective map
followed by an injective map, we obtain that any morphism of sheaves in `Sheaf J A`
factors in a functorial manner as a locally surjective morphism (which is epi) followed by
a locally injective morphism (which is mono).

Moreover, if we assume that the category of sheaves `Sheaf J A` is balanced
(see `Sites.LeftExact`), then epimorphisms are exactly locally surjective morphisms.

-/

universe w v' u' v u

namespace CategoryTheory

open Category ConcreteCategory Functor

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (A : Type u') [Category.{v'} A] {FA : A → A → Type*} {CA : A → Type w}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w} A FA]
  [HasFunctorialSurjectiveInjectiveFactorization A]
  [J.WEqualsLocallyBijective A]

namespace Sheaf

def locallyInjective : MorphismProperty (Sheaf J A) :=
  fun _ _ f => IsLocallyInjective f

def locallySurjective : MorphismProperty (Sheaf J A) :=
  fun _ _ f => IsLocallySurjective f

variable {A}

variable (data : FunctorialSurjectiveInjectiveFactorizationData A) [HasWeakSheafify J A]

set_option backward.isDefEq.respectTransparency false in

noncomputable def functorialLocallySurjectiveInjectiveFactorization :
    (locallySurjective J A).FunctorialFactorizationData (locallyInjective J A) where
  Z := (sheafToPresheaf J A).mapArrow ⋙ (data.functorCategory Cᵒᵖ).Z ⋙ presheafToSheaf J A
  i := whiskerLeft Arrow.leftFunc (inv (sheafificationAdjunction J A).counit) ≫
        whiskerLeft (sheafToPresheaf J A).mapArrow
          (whiskerRight (data.functorCategory Cᵒᵖ).i (presheafToSheaf J A))
  p := whiskerLeft (sheafToPresheaf J A).mapArrow
        (whiskerRight (data.functorCategory Cᵒᵖ).p (presheafToSheaf J A)) ≫
          whiskerLeft Arrow.rightFunc (sheafificationAdjunction J A).counit
  fac := by
    ext f : 2
    dsimp
    simp only [assoc, ← Functor.map_comp_assoc,
      MorphismProperty.FunctorialFactorizationData.fac_app,
      NatIso.isIso_inv_app, IsIso.inv_comp_eq]
    exact (sheafificationAdjunction J A).counit.naturality f.hom
  hi _ := by
    dsimp [locallySurjective]
    rw [← isLocallySurjective_sheafToPresheaf_map_iff, Functor.map_comp,
      Presheaf.comp_isLocallySurjective_iff, isLocallySurjective_sheafToPresheaf_map_iff,
      Presheaf.isLocallySurjective_presheafToSheaf_map_iff]
    apply Presheaf.isLocallySurjective_of_surjective
    apply (data.functorCategory Cᵒᵖ).hi
  hp _ := by
    dsimp [locallyInjective]
    rw [← isLocallyInjective_sheafToPresheaf_map_iff, Functor.map_comp,
      Presheaf.isLocallyInjective_comp_iff, isLocallyInjective_sheafToPresheaf_map_iff,
      Presheaf.isLocallyInjective_presheafToSheaf_map_iff]
    apply Presheaf.isLocallyInjective_of_injective
    apply (data.functorCategory Cᵒᵖ).hp

variable (f : Arrow (Sheaf J A))

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

variable [J.HasSheafCompose (forget A)]

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

end

-- INSTANCE (free from Core): :

end

variable {J}

variable [HasSheafify J A] [J.HasSheafCompose (forget A)] [Balanced (Sheaf J A)]

variable {F G : Sheaf J A} (φ : F ⟶ G)

lemma isLocallySurjective_iff_epi' :
    IsLocallySurjective φ ↔ Epi φ := by
  constructor
  · intro
    infer_instance
  · intro
    let data := (locallySurjective J A).factorizationData (locallyInjective J A) φ
    have : IsLocallySurjective data.i := data.hi
    have : IsLocallyInjective data.p := data.hp
    have : Epi data.p := epi_of_epi_fac data.fac
    have := mono_of_isLocallyInjective data.p
    have := isIso_of_mono_of_epi data.p
    rw [← data.fac]
    infer_instance

end

end Sheaf

end CategoryTheory
