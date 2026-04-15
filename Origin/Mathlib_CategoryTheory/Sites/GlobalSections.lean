/-
Extracted from CategoryTheory/Sites/GlobalSections.lean
Genuine: 10 of 12 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Global sections of sheaves

In this file we define a global sections functor `Sheaf.Γ : Sheaf J A ⥤ A` and show that it
is isomorphic to several other constructions when they exist, most notably evaluation of sheaves
on a terminal object and `Functor.sectionsFunctor`.

## Main definitions / results

* `HasGlobalSectionsFunctor J A`: typeclass stating that the constant sheaf functor `A ⥤ Sheaf J A`
  has a right-adjoint.
* `Sheaf.Γ J A`: the global sections functor `Sheaf J A ⥤ A`, defined as the right-adjoint of the
  constant sheaf functor, whenever that exists.
* `constantSheafΓAdj J A`: the adjunction between the constant sheaf functor and `Sheaf.Γ J A`.
* `Sheaf.ΓNatIsoSheafSections J A hT`: on sites with a terminal object `T`, `Sheaf.Γ J A` exists and
  is isomorphic to the functor evaluating sheaves at `T`.
* `Sheaf.ΓNatIsoLim J A`: when `A` has limits of shape `Cᵒᵖ`, `Sheaf.Γ J A` exists and is isomorphic
  to the functor taking each sheaf to the limit of its underlying presheaf.
* `Sheaf.isLimitConeΓ F`: global sections are limits even when not all limits of shape `Cᵒᵖ` exist.
* `Sheaf.ΓRes F U`: the restriction morphism from global sections of `F` to sections of `F` on `U`.
* `Sheaf.natTransΓRes J A U`: the natural transformation from the global sections functor to
  the sections functor on `U`.
* `Sheaf.ΓNatIsoSectionsFunctor J`: for sheaves of types, `Sheaf.Γ J A` is isomorphic to the
  functor taking each sheaf to the type of sections of its underlying presheaf in the sense of
  `Functor.sections`.
* `Sheaf.ΓNatIsoCoyoneda J`: for sheaves of types, `Sheaf.Γ J A` is isomorphic to the
  coyoneda embedding of the terminal sheaf, i.e. the functor sending each sheaf `F` to the type
  of morphisms from the terminal sheaf to `F`.

## TODO

* Generalise `Sheaf.ΓNatIsoSectionsFunctor` and `Sheaf.ΓNatIsoCoyoneda` from `Type max u v` to
  `Type max u v w`. This should hopefully be doable by relaxing the universe constraints of
  `instHasSheafifyOfHasFiniteLimits`.

-/

universe u v w u₂ v₂

open CategoryTheory Limits Sheaf Opposite GrothendieckTopology

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (A : Type u₂) [Category.{v₂} A] [HasWeakSheafify J A]

abbrev HasGlobalSectionsFunctor := (constantSheaf J A).IsLeftAdjoint

noncomputable def Sheaf.Γ [HasGlobalSectionsFunctor J A] : Sheaf J A ⥤ A :=
  (constantSheaf J A).rightAdjoint

deriving Functor.IsRightAdjoint

noncomputable def constantSheafΓAdj [HasGlobalSectionsFunctor J A] :
    constantSheaf J A ⊣ Γ J A :=
  Adjunction.ofIsLeftAdjoint (constantSheaf J A)

-- INSTANCE (free from Core): hasGlobalSectionsFunctor_of_hasTerminal

noncomputable def Sheaf.ΓNatIsoSheafSections [HasTerminal C] {T : C} (hT : IsTerminal T) :
    Γ J A ≅ (sheafSections J A).obj (op T) :=
  (constantSheafΓAdj J A).rightAdjointUniq (constantSheafAdj J A hT)

-- INSTANCE (free from Core): hasGlobalSectionsFunctor_of_hasLimitsOfShape

noncomputable def Sheaf.ΓNatIsoLim [HasLimitsOfShape Cᵒᵖ A] :
    Γ J A ≅ sheafToPresheaf J A ⋙ lim :=
  (constantSheafΓAdj J A).rightAdjointUniq (constLimAdj.comp (sheafificationAdjunction J A))

variable {J A}

noncomputable def Sheaf.ΓHomEquiv [HasGlobalSectionsFunctor J A] {X : A} {F : Sheaf J A} :
    ((Functor.const _).obj X ⟶ F.obj) ≃ (X ⟶ (Γ J A).obj F) :=
  ((sheafificationAdjunction J A).homEquiv _ _).symm.trans
    ((constantSheafΓAdj J A).homEquiv _ _)

lemma Sheaf.ΓHomEquiv_naturality_left [HasGlobalSectionsFunctor J A] {X' X : A} {F : Sheaf J A}
    (f : X' ⟶ X) (g : (Functor.const _).obj X ⟶ F.obj) :
    ΓHomEquiv ((Functor.const _).map f ≫ g) = f ≫ ΓHomEquiv g :=
  (congrArg _ ((sheafificationAdjunction J A).homEquiv_naturality_left_symm _ _)).trans
    ((constantSheafΓAdj J A).homEquiv_naturality_left _ _)

lemma Sheaf.ΓHomEquiv_naturality_left_symm [HasGlobalSectionsFunctor J A] {X' X : A} {F : Sheaf J A}
    (f : X' ⟶ X) (g : X ⟶ (Γ J A).obj F) :
    ΓHomEquiv.symm (f ≫ g) = (Functor.const _).map f ≫ ΓHomEquiv.symm g :=
  (congrArg _ ((constantSheafΓAdj J A).homEquiv_naturality_left_symm _ _)).trans
    ((sheafificationAdjunction J A).homEquiv_naturality_left _ _)

lemma Sheaf.ΓHomEquiv_naturality_right [HasGlobalSectionsFunctor J A] {X : A} {F F' : Sheaf J A}
    (f : (Functor.const _).obj X ⟶ F.obj) (g : F ⟶ F') :
    ΓHomEquiv (f ≫ g.hom) = ΓHomEquiv f ≫ (Γ J A).map g :=
  (congrArg _ ((sheafificationAdjunction J A).homEquiv_naturality_right_symm _ _)).trans
    ((constantSheafΓAdj J A).homEquiv_naturality_right _ _)

lemma Sheaf.ΓHomEquiv_naturality_right_symm [HasGlobalSectionsFunctor J A] {X : A}
    {F F' : Sheaf J A} (f : X ⟶ (Γ J A).obj F) (g : F ⟶ F') :
    ΓHomEquiv.symm (f ≫ (Γ J A).map g) = ΓHomEquiv.symm f ≫ g.hom :=
  (congrArg _ ((constantSheafΓAdj J A).homEquiv_naturality_right_symm _ _)).trans
    ((sheafificationAdjunction J A).homEquiv_naturality_right _ _)
