/-
Extracted from CategoryTheory/Groupoid/FreeGroupoidOfCategory.lean
Genuine: 8 of 11 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Free groupoid on a category

This file defines the free groupoid on a category, the lifting of a functor to its unique
extension as a functor from the free groupoid, and proves uniqueness of this extension.

## Main results

Given a type `C` and a category instance on `C`:

- `CategoryTheory.FreeGroupoid C`: the underlying type of the free groupoid on `C`.
- `CategoryTheory.FreeGroupoid.instGroupoid`: the `Groupoid` instance on `FreeGroupoid C`.
- `CategoryTheory.FreeGroupoid.lift`: the lifting of a functor `C ⥤ G` where `G` is a
  groupoid, to a functor `CategoryTheory.FreeGroupoid C ⥤ G`.
- `CategoryTheory.FreeGroupoid.lift_spec` and
  `CategoryTheory.FreeGroupoid.lift_unique`:
  the proofs that, respectively, `CategoryTheory.FreeGroupoid.lift` indeed is a lifting
  and is the unique one.
- `CategoryTheory.Grpd.free`: the free functor from `Grpd` to `Cat`
- `CategoryTheory.Grpd.freeForgetAdjunction`: that `free` is left adjoint to
  `Grpd.forgetToCat`.

## Implementation notes

The free groupoid on a category `C` is first defined by taking the free groupoid `G`
on the underlying *quiver* of `C`. Then the free groupoid on the *category* `C` is defined as
the quotient of `G` by the relation that makes the inclusion prefunctor `C ⥤q G` a functor.

-/

noncomputable section

namespace CategoryTheory

universe v u v₁ u₁ v₂ u₂

variable (C : Type u) [Category.{v} C]

open Quiver in

inductive FreeGroupoid.homRel : HomRel (Quiver.FreeGroupoid C) where
| map_id (X : C) : homRel ((FreeGroupoid.of C).map (𝟙 X)) (𝟙 ((FreeGroupoid.of C).obj X))
| map_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : homRel ((FreeGroupoid.of C).map (f ≫ g))
  ((FreeGroupoid.of C).map f ≫ (FreeGroupoid.of C).map g)

def FreeGroupoid := Quotient (FreeGroupoid.homRel C)

-- INSTANCE (free from Core): [Nonempty

-- INSTANCE (free from Core): :

namespace FreeGroupoid

def of : C ⥤ FreeGroupoid C where
  __ := Quiver.FreeGroupoid.of C ⋙q (Quotient.functor (FreeGroupoid.homRel C)).toPrefunctor
  map_id X := Quotient.sound _ (FreeGroupoid.homRel.map_id X)
  map_comp f g := Quotient.sound _ (FreeGroupoid.homRel.map_comp f g)

variable {C}

abbrev mk (X : C) : FreeGroupoid C := (of C).obj X

abbrev homMk {X Y : C} (f : X ⟶ Y) : mk X ⟶ mk Y := (of C).map f

lemma of_obj_bijective : Function.Bijective (of C).obj where
  left _ _ h := by cases h; rfl
  right X := ⟨X.as.as, rfl⟩

section UniversalProperty

variable {G : Type u₁} [Groupoid.{v₁} G]

set_option backward.isDefEq.respectTransparency false in

def lift (φ : C ⥤ G) : FreeGroupoid C ⥤ G :=
  Quotient.lift (FreeGroupoid.homRel C) (Quiver.FreeGroupoid.lift φ.toPrefunctor)
    (fun _ _ f g r ↦ by
      have {X Y : C} (f : X ⟶ Y) :=
        Prefunctor.congr_hom (Quiver.FreeGroupoid.lift_spec φ.toPrefunctor) f
      induction r <;> cat_disch)

set_option backward.isDefEq.respectTransparency false in

theorem lift_spec (φ : C ⥤ G) : of C ⋙ lift φ = φ :=
  Functor.toPrefunctor_injective (by
    change Quiver.FreeGroupoid.of C ⋙q
      (Quotient.functor (FreeGroupoid.homRel C)).toPrefunctor ⋙q
        (lift φ).toPrefunctor = φ.toPrefunctor
    simp [lift, Quotient.lift_spec, Quiver.FreeGroupoid.lift_spec])
