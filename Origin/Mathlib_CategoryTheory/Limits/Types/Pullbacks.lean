/-
Extracted from CategoryTheory/Limits/Types/Pullbacks.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Pullbacks in the category of types

In `Type*`, the pullback of `f : X ⟶ Z` and `g : Y ⟶ Z` is the
subtype `{ p : X × Y // f p.1 = g p.2 }` of the product.
We show some additional lemmas for pullbacks in the category of types.
-/

universe v u

open CategoryTheory Limits ConcreteCategory

namespace CategoryTheory.Limits.Types

variable {X Y Z : Type u} {X' Y' Z' : Type v}

variable (f : X ⟶ Z) (g : Y ⟶ Z) (f' : X' ⟶ Z') (g' : Y' ⟶ Z')

abbrev PullbackObj : Type u :=
  { p : X × Y // f p.1 = g p.2 }

example (p : PullbackObj f g) : X × Y :=

  p

abbrev pullbackCone : Limits.PullbackCone f g :=
  PullbackCone.mk (TypeCat.ofHom (fun p : PullbackObj f g => p.1.1))
    (TypeCat.ofHom (fun p => p.1.2)) (by ext p; exact p.2)
