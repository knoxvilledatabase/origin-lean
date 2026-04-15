/-
Extracted from CategoryTheory/Localization/Bousfield.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Bousfield localization

Given a predicate `P : ObjectProperty C` on the objects of a category `C`,
we define `W.isLocal : MorphismProperty C` as the class of morphisms `f : X ⟶ Y`
such that for any `Z : C` such that `P Z`, the precomposition with `f`
induces a bijection `(Y ⟶ Z) ≃ (X ⟶ Z)`.

(This construction is part of the left Bousfield localization
in the context of model categories.)

When `G ⊣ F` is an adjunction with `F : C ⥤ D` fully faithful, then
`G : D ⥤ C` is a localization functor for the class `isLocal (· ∈ Set.range F.obj)`,
which then identifies to the inverse image by `G` of the class of
isomorphisms in `C`.

The dual results are also obtained.

## References

* https://ncatlab.org/nlab/show/left+Bousfield+localization+of+model+categories

-/

namespace CategoryTheory

open Category

variable {C D : Type*} [Category* C] [Category* D]

namespace ObjectProperty

/-! ### Left Bousfield localization -/

variable (P : ObjectProperty C)

def isLocal : MorphismProperty C := fun _ _ f =>
  ∀ Z, P Z → Function.Bijective (fun (g : _ ⟶ Z) => f ≫ g)

variable {P} in
