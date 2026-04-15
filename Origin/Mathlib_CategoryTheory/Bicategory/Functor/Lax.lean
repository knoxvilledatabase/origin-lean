/-
Extracted from CategoryTheory/Bicategory/Functor/Lax.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Lax functors

A lax functor `F` between bicategories `B` and `C` consists of
* a function between objects `F.obj : B → C`,
* a family of functions between 1-morphisms `F.map : (a ⟶ b) → (F.obj a ⟶ F.obj b)`,
* a family of functions between 2-morphisms `F.map₂ : (f ⟶ g) → (F.map f ⟶ F.map g)`,
* a family of 2-morphisms `F.mapId a : 𝟙 (F.obj a) ⟶ F.map (𝟙 a)`,
* a family of 2-morphisms `F.mapComp f g : F.map f ≫ F.map g ⟶ F.map (f ≫ g)`, and
* certain consistency conditions on them.

## Main definitions

* `CategoryTheory.LaxFunctor B C` : a lax functor between bicategories `B` and `C`, which we
  denote by `B ⥤ᴸ C`.
* `CategoryTheory.LaxFunctor.comp F G` : the composition of lax functors
* `CategoryTheory.LaxFunctor.PseudoCore` : a structure on a lax functor that promotes a
  lax functor to a pseudofunctor

## Future work

Some constructions in the bicategory library have only been done in terms of oplax functors,
since lax functors had not yet been added (e.g `FunctorBicategory.lean`). A possible project would
be to mirror these constructions for lax functors.

-/

namespace CategoryTheory

open Category Bicategory

open Bicategory

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

structure LaxFunctor (B : Type u₁) [Bicategory.{w₁, v₁} B] (C : Type u₂) [Bicategory.{w₂, v₂} C]
    extends PrelaxFunctor B C where
  /-- The 2-morphism underlying the lax unity constraint. -/
  mapId (a : B) : 𝟙 (obj a) ⟶ map (𝟙 a)
  /-- The 2-morphism underlying the lax functoriality constraint. -/
  mapComp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) : map f ≫ map g ⟶ map (f ≫ g)
  /-- Naturality of the lax functoriality constraint, on the left. -/
  mapComp_naturality_left :
    ∀ {a b c : B} {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c),
      mapComp f g ≫ map₂ (η ▷ g) = map₂ η ▷ map g ≫ mapComp f' g := by cat_disch
  /-- Naturality of the lax functoriality constraint, on the right. -/
  mapComp_naturality_right :
    ∀ {a b c : B} (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g'),
     mapComp f g ≫ map₂ (f ◁ η) = map f ◁ map₂ η ≫ mapComp f g' := by cat_disch
  /-- Lax associativity. -/
  map₂_associator :
    ∀ {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d),
      mapComp f g ▷ map h ≫ mapComp (f ≫ g) h ≫ map₂ (α_ f g h).hom =
      (α_ (map f) (map g) (map h)).hom ≫ map f ◁ mapComp g h ≫ mapComp f (g ≫ h) := by cat_disch
  /-- Lax left unity. -/
  map₂_leftUnitor :
    ∀ {a b : B} (f : a ⟶ b),
      map₂ (λ_ f).inv = (λ_ (map f)).inv ≫ mapId a ▷ map f ≫ mapComp (𝟙 a) f := by cat_disch
  /-- Lax right unity. -/
  map₂_rightUnitor :
    ∀ {a b : B} (f : a ⟶ b),
      map₂ (ρ_ f).inv = (ρ_ (map f)).inv ≫ map f ◁ mapId b ≫ mapComp f (𝟙 b) := by cat_disch

scoped[CategoryTheory.Bicategory] infixr:26 " ⥤ᴸ " => LaxFunctor -- type as \func\^L

initialize_simps_projections LaxFunctor (+toPrelaxFunctor, -obj, -map, -map₂)

namespace LaxFunctor

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]

attribute [to_app (attr := reassoc (attr := simp))]

  mapComp_naturality_left mapComp_naturality_right map₂_associator

attribute [simp, to_app (attr := reassoc)] map₂_leftUnitor map₂_rightUnitor

add_decl_doc LaxFunctor.toPrelaxFunctor

variable (F : B ⥤ᴸ C)
