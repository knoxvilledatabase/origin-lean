/-
Extracted from CategoryTheory/Subobject/MonoOver.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Monomorphisms over a fixed object

As preparation for defining `Subobject X`, we set up the theory for
`MonoOver X := { f : Over X // Mono f.hom}`.

Here `MonoOver X` is a thin category (a pair of objects has at most one morphism between them),
so we can think of it as a preorder. However as it is not skeletal, it is not yet a partial order.

`Subobject X` will be defined as the skeletalization of `MonoOver X`.

We provide
* `def pullback [HasPullbacks C] (f : X ⟶ Y) : MonoOver Y ⥤ MonoOver X`
* `def map (f : X ⟶ Y) [Mono f] : MonoOver X ⥤ MonoOver Y`
* `def «exists» [HasImages C] (f : X ⟶ Y) : MonoOver X ⥤ MonoOver Y`

and prove their basic properties and relationships.

## Notes

This development originally appeared in Bhavik Mehta's "Topos theory for Lean" repository,
and was ported to mathlib by Kim Morrison.

-/

universe w' w v₁ v₂ v₃ u₁ u₂ u₃

noncomputable section

namespace CategoryTheory

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] {X Y Z : C}

variable {D : Type u₂} [Category.{v₂} D]

abbrev Over.isMono (X : C) : ObjectProperty (Over X) :=
  fun f : Over X => Mono f.hom

abbrev MonoOver (X : C) := (Over.isMono X).FullSubcategory

namespace MonoOver

-- INSTANCE (free from Core): mono_obj_hom
