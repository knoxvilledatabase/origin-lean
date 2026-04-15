/-
Extracted from CategoryTheory/Functor/KanExtension/Basic.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Kan extensions

The basic definitions for Kan extensions of functors are introduced in this file. Part of API
is parallel to the definitions for bicategories (see `CategoryTheory.Bicategory.Kan.IsKan`).
(The bicategory API cannot be used directly here because it would not allow the universe
polymorphism which is necessary for some applications.)

Given a natural transformation `α : L ⋙ F' ⟶ F`, we define the property
`F'.IsRightKanExtension α` which expresses that `(F', α)` is a right Kan
extension of `F` along `L`, i.e. that it is a terminal object in a
category `RightExtension L F` of costructured arrows. The condition
`F'.IsLeftKanExtension α` for `α : F ⟶ L ⋙ F'` is defined similarly.

We also introduce typeclasses `HasRightKanExtension L F` and `HasLeftKanExtension L F`
which assert the existence of a right or left Kan extension, and chosen Kan extensions
are obtained as `leftKanExtension L F` and `rightKanExtension L F`.

## References
* https://ncatlab.org/nlab/show/Kan+extension

-/

namespace CategoryTheory

open Category Limits Functor

namespace Functor

variable {C C' H D D' : Type*}
  [Category* C] [Category* C'] [Category* H] [Category* D] [Category* D']

abbrev RightExtension (L : C ⥤ D) (F : C ⥤ H) :=
  CostructuredArrow ((whiskeringLeft C D H).obj L) F

abbrev LeftExtension (L : C ⥤ D) (F : C ⥤ H) :=
  StructuredArrow F ((whiskeringLeft C D H).obj L)
