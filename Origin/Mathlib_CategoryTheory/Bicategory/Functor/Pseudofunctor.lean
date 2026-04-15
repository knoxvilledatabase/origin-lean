/-
Extracted from CategoryTheory/Bicategory/Functor/Pseudofunctor.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Pseudofunctors

A pseudofunctor is an oplax (or lax) functor whose `mapId` and `mapComp` are isomorphisms.
We provide several constructors for pseudofunctors:
* `Pseudofunctor.mk` : the default constructor, which requires `map₂_whiskerLeft` and
  `map₂_whiskerRight` instead of naturality of `mapComp`.

* `Pseudofunctor.mkOfOplax` : construct a pseudofunctor from an oplax functor whose
  `mapId` and `mapComp` are isomorphisms. This constructor uses `Iso` to describe isomorphisms.
* `Pseudofunctor.mkOfOplax'` : similar to `mkOfOplax`, but uses `IsIso` to describe isomorphisms.

* `Pseudofunctor.mkOfLax` : construct a pseudofunctor from a lax functor whose
  `mapId` and `mapComp` are isomorphisms. This constructor uses `Iso` to describe isomorphisms.
* `Pseudofunctor.mkOfLax'` : similar to `mkOfLax`, but uses `IsIso` to describe isomorphisms.

## Main definitions

* `CategoryTheory.Pseudofunctor B C` : a pseudofunctor between bicategories `B` and `C`, which we
  denote by `B ⥤ᵖ C`.
* `CategoryTheory.Pseudofunctor.comp F G` : the composition of pseudofunctors

-/

namespace CategoryTheory

open Category Bicategory

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]

variable {D : Type u₃} [Bicategory.{w₃, v₃} D]

structure Pseudofunctor (B : Type u₁) [Bicategory.{w₁, v₁} B] (C : Type u₂)
    [Bicategory.{w₂, v₂} C] extends PrelaxFunctor B C where
  mapId (a : B) : map (𝟙 a) ≅ 𝟙 (obj a)
  mapComp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) : map (f ≫ g) ≅ map f ≫ map g
  map₂_whisker_left :
    ∀ {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h),
      map₂ (f ◁ η) = (mapComp f g).hom ≫ map f ◁ map₂ η ≫ (mapComp f h).inv := by
    cat_disch
  map₂_whisker_right :
    ∀ {a b c : B} {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c),
      map₂ (η ▷ h) = (mapComp f h).hom ≫ map₂ η ▷ map h ≫ (mapComp g h).inv := by
    cat_disch
  map₂_associator :
    ∀ {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d),
      map₂ (α_ f g h).hom = (mapComp (f ≫ g) h).hom ≫ (mapComp f g).hom ▷ map h ≫
      (α_ (map f) (map g) (map h)).hom ≫ map f ◁ (mapComp g h).inv ≫
      (mapComp f (g ≫ h)).inv := by
    cat_disch
  map₂_left_unitor :
    ∀ {a b : B} (f : a ⟶ b),
      map₂ (λ_ f).hom = (mapComp (𝟙 a) f).hom ≫ (mapId a).hom ▷ map f ≫ (λ_ (map f)).hom := by
    cat_disch
  map₂_right_unitor :
    ∀ {a b : B} (f : a ⟶ b),
      map₂ (ρ_ f).hom = (mapComp f (𝟙 b)).hom ≫ map f ◁ (mapId b).hom ≫ (ρ_ (map f)).hom := by
    cat_disch

scoped[CategoryTheory.Bicategory] infixr:26 " ⥤ᵖ " => Pseudofunctor -- type as \func\^p

initialize_simps_projections Pseudofunctor (+toPrelaxFunctor, -obj, -map, -map₂)

namespace Pseudofunctor

attribute [simp, to_app (attr := reassoc)]

  map₂_whisker_left map₂_whisker_right map₂_associator map₂_left_unitor map₂_right_unitor

open Iso

add_decl_doc Pseudofunctor.toPrelaxFunctor

attribute [nolint docBlame] CategoryTheory.Pseudofunctor.mapId

  CategoryTheory.Pseudofunctor.mapComp

  CategoryTheory.Pseudofunctor.map₂_whisker_left

  CategoryTheory.Pseudofunctor.map₂_whisker_right

  CategoryTheory.Pseudofunctor.map₂_associator

  CategoryTheory.Pseudofunctor.map₂_left_unitor

  CategoryTheory.Pseudofunctor.map₂_right_unitor

variable (F : B ⥤ᵖ C)
