/-
Extracted from CategoryTheory/Functor/TwoSquare.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# 2-squares of functors

Given four functors `T`, `L`, `R` and `B`, a 2-square `TwoSquare T L R B` consists of
a natural transformation `w : T ⋙ R ⟶ L ⋙ B`:
```
     T
  C₁ ⥤ C₂
L |     | R
  v     v
  C₃ ⥤ C₄
     B
```

We define operations to paste such squares horizontally and vertically and prove the interchange
law of those two operations.

## TODO

Generalize all of this to double categories.

-/

universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉

namespace CategoryTheory

open Category Functor

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃] [Category.{v₄} C₄]
  (T : C₁ ⥤ C₂) (L : C₁ ⥤ C₃) (R : C₂ ⥤ C₄) (B : C₃ ⥤ C₄)

def TwoSquare := T ⋙ R ⟶ L ⋙ B

namespace TwoSquare

abbrev mk (α : T ⋙ R ⟶ L ⋙ B) : TwoSquare T L R B := α

variable {T} {L} {R} {B} in

abbrev natTrans (w : TwoSquare T L R B) : T ⋙ R ⟶ L ⋙ B := w
