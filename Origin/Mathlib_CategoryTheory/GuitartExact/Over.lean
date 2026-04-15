/-
Extracted from CategoryTheory/GuitartExact/Over.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Guitart exact squares involving `Over` categories

Let `F : C ⥤ D` be a functor and `X : C`. One may consider the
commutative square of categories where vertical functors are `Over.forget`:
```
    Over.post F
Over X ⥤ Over (F.obj X)
 |          |
 v          v
 C     ⥤    D
       F
```

We show that this square is Guitart exact if for all `Y : C`, the binary product `X ⨯ Y`
exists and `F` commutes with it.

-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (F : C ⥤ D) (X : C)

abbrev TwoSquare.overPost :
    TwoSquare (Over.post F) (Over.forget X) (Over.forget (F.obj X)) F :=
  TwoSquare.mk _ _ _ _ (𝟙 _)

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): [∀

end CategoryTheory
