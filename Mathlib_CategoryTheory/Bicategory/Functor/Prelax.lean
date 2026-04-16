/-
Extracted from CategoryTheory/Bicategory/Functor/Prelax.lean
Genuine: 13 | Conflates: 0 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core
import Mathlib.CategoryTheory.Bicategory.Basic

noncomputable section

/-!

# Prelax functors

This file defines lax prefunctors and prelax functors between bicategories. The point of these
definitions is to provide some common API that will be helpful in the development of both lax and
oplax functors.

## Main definitions

`PrelaxFunctorStruct B C`:

A PrelaxFunctorStruct `F` between quivers `B` and `C`, such that both have been equipped with quiver
structures on the hom-types, consists of
* a function between objects `F.obj : B ⟶ C`,
* a family of functions between 1-morphisms `F.map : (a ⟶ b) → (F.obj a ⟶ F.obj b)`,
* a family of functions between 2-morphisms `F.map₂ : (f ⟶ g) → (F.map f ⟶ F.map g)`,

`PrelaxFunctor B C`:

A prelax functor `F` between bicategories `B` and `C` is a `PrelaxFunctorStruct` such that the
associated prefunctors between the hom types are all functors. In other words, it is a
`PrelaxFunctorStruct` that satisfies
* `F.map₂ (𝟙 f) = 𝟙 (F.map f)`,
* `F.map₂ (η ≫ θ) = F.map₂ η ≫ F.map₂ θ`.

`mkOfHomFunctor`: constructs a `PrelaxFunctor` from a map on objects and functors between the
corresponding hom types.

-/

namespace CategoryTheory

open Category Bicategory

open Bicategory

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

section

variable (B : Type u₁) [Quiver.{v₁ + 1} B] [∀ a b : B, Quiver.{w₁ + 1} (a ⟶ b)]

variable (C : Type u₂) [Quiver.{v₂ + 1} C] [∀ a b : C, Quiver.{w₂ + 1} (a ⟶ b)]

variable {D : Type u₃} [Quiver.{v₃ + 1} D] [∀ a b : D, Quiver.{w₃ + 1} (a ⟶ b)]

structure PrelaxFunctorStruct extends Prefunctor B C where
  /-- The action of a lax prefunctor on 2-morphisms. -/
  map₂ {a b : B} {f g : a ⟶ b} : (f ⟶ g) → (map f ⟶ map g)

initialize_simps_projections PrelaxFunctorStruct (+toPrefunctor, -obj, -map)

variable {B} {C}

namespace PrelaxFunctorStruct

@[simps]
def mkOfHomPrefunctors (F : B → C) (F' : (a : B) → (b : B) → Prefunctor (a ⟶ b) (F a ⟶ F b)) :
    PrelaxFunctorStruct B C where
  obj := F
  map {a b} := (F' a b).obj
  map₂ {a b} := (F' a b).map

@[simps]
def id (B : Type u₁) [Quiver.{v₁ + 1} B] [∀ a b : B, Quiver.{w₁ + 1} (a ⟶ b)] :
    PrelaxFunctorStruct B B :=
  { Prefunctor.id B with map₂ := fun η => η }

instance : Inhabited (PrelaxFunctorStruct B B) :=
  ⟨PrelaxFunctorStruct.id B⟩

@[simps]
def comp (F : PrelaxFunctorStruct B C) (G : PrelaxFunctorStruct C D) : PrelaxFunctorStruct B D where
  toPrefunctor := F.toPrefunctor.comp G.toPrefunctor
  map₂ := fun η => G.map₂ (F.map₂ η)

end PrelaxFunctorStruct

end

structure PrelaxFunctor (B : Type u₁) [Bicategory.{w₁, v₁} B] (C : Type u₂) [Bicategory.{w₂, v₂} C]
    extends PrelaxFunctorStruct B C where
  /-- Prelax functors preserves identity 2-morphisms. -/
  map₂_id : ∀ {a b : B} (f : a ⟶ b), map₂ (𝟙 f) = 𝟙 (map f) := by aesop -- TODO: why not aesop_cat?
  /-- Prelax functors preserves compositions of 2-morphisms. -/
  map₂_comp : ∀ {a b : B} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h),
      map₂ (η ≫ θ) = map₂ η ≫ map₂ θ := by aesop_cat

namespace PrelaxFunctor

initialize_simps_projections PrelaxFunctor (+toPrelaxFunctorStruct, -obj, -map, -map₂)

attribute [simp] map₂_id

attribute [reassoc] map₂_comp

attribute [simp] map₂_comp

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]

variable {D : Type u₃} [Bicategory.{w₃, v₃} D]

@[simps]
def mkOfHomFunctors (F : B → C) (F' : (a : B) → (b : B) → (a ⟶ b) ⥤ (F a ⟶ F b)) :
    PrelaxFunctor B C where
  toPrelaxFunctorStruct := PrelaxFunctorStruct.mkOfHomPrefunctors F fun a b => (F' a b).toPrefunctor
  map₂_id {a b} := (F' a b).map_id
  map₂_comp {a b} := (F' a b).map_comp

@[simps]
def id (B : Type u₁) [Bicategory.{w₁, v₁} B] : PrelaxFunctor B B where
  toPrelaxFunctorStruct := PrelaxFunctorStruct.id B

instance : Inhabited (PrelaxFunctorStruct B B) :=
  ⟨PrelaxFunctorStruct.id B⟩

variable (F : PrelaxFunctor B C)

@[simps]
def comp (G : PrelaxFunctor C D) : PrelaxFunctor B D where
  toPrelaxFunctorStruct := PrelaxFunctorStruct.comp F.toPrelaxFunctorStruct G.toPrelaxFunctorStruct

@[simps]
def mapFunctor (a b : B) : (a ⟶ b) ⥤ (F.obj a ⟶ F.obj b) where
  obj f := F.map f
  map η := F.map₂ η

@[simp]
lemma mkOfHomFunctors_mapFunctor (F : B → C) (F' : (a : B) → (b : B) → (a ⟶ b) ⥤ (F a ⟶ F b))
    (a b : B) : (mkOfHomFunctors F F').mapFunctor a b = F' a b :=
  rfl

section

variable {a b : B}

@[simps!]
abbrev map₂Iso {f g : a ⟶ b} (η : f ≅ g) : F.map f ≅ F.map g :=
  (F.mapFunctor a b).mapIso η

instance map₂_isIso {f g : a ⟶ b} (η : f ⟶ g) [IsIso η] : IsIso (F.map₂ η) :=
  (F.map₂Iso (asIso η)).isIso_hom

@[simp]
lemma map₂_inv {f g : a ⟶ b} (η : f ⟶ g) [IsIso η] : F.map₂ (inv η) = inv (F.map₂ η) := by
  apply IsIso.eq_inv_of_hom_inv_id
  simp [← F.map₂_comp η (inv η)]

@[reassoc, simp]
lemma map₂_hom_inv {f g : a ⟶ b} (η : f ≅ g) :
    F.map₂ η.hom ≫ F.map₂ η.inv = 𝟙 (F.map f) := by
  rw [← F.map₂_comp, Iso.hom_inv_id, F.map₂_id]

@[reassoc, simp]
lemma map₂_inv_hom {f g : a ⟶ b} (η : f ≅ g) :
    F.map₂ η.inv ≫ F.map₂ η.hom = 𝟙 (F.map g) := by
  rw [← F.map₂_comp, Iso.inv_hom_id, F.map₂_id]

end

end PrelaxFunctor

end CategoryTheory
