/-
Extracted from CategoryTheory/ObjectProperty/Local.lean
Genuine: 2 of 8 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core

/-!
# Objects that are local with respect to a property of morphisms

Given `W : MorphismProperty C`, we define `W.isLocal : ObjectProperty C`
which is the property of objects `Z` such that for any `f : X ⟶ Y` satisfying `W`,
the precomposition with `f` gives a bijection `(Y ⟶ Z) ≃ (X ⟶ Z)`.
(In the file `Mathlib/CategoryTheory/Localization/Bousfield.lean`, it is shown that this is
part of a Galois connection, with "dual" construction
`ObjectProperty.isLocal : ObjectProperty C → MorphismProperty C`.)

We also introduce the dual notion `W.isColocal : ObjectProperty C`.

-/

universe v v' u u'

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

namespace MorphismProperty

variable (W : MorphismProperty C)

def isLocal : ObjectProperty C :=
  fun Z ↦ ∀ ⦃X Y : C⦄ (f : X ⟶ Y),
    W f → Function.Bijective (fun (g : _ ⟶ Z) ↦ f ≫ g)

def isColocal : ObjectProperty C :=
  fun X ↦ ∀ ⦃Y Z : C⦄ (g : Y ⟶ Z),
    W g → Function.Bijective (fun (f : X ⟶ _) ↦ f ≫ g)

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): (J

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): (J

end MorphismProperty

end CategoryTheory
