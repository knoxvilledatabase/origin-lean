/-
Extracted from CategoryTheory/Category/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Categories

Defines a category, as a type class parametrised by the type of objects.

## Notation

Introduces notations in the `CategoryTheory` scope
* `X ⟶ Y` for the morphism spaces (type as `\hom`),
* `𝟙 X` for the identity morphism on `X` (type as `\b1`),
* `f ≫ g` for composition in the 'arrows' convention (type as `\gg`).

Users may like to add `g ⊚ f` for composition in the standard convention, using
```lean
local notation:80 g " ⊚ " f:80 => CategoryTheory.CategoryStruct.comp f g    -- type as \oo
```

-/

library_note «category theory universes»

library_note «universe output parameters and typeclass caching»

universe v u

namespace CategoryTheory
