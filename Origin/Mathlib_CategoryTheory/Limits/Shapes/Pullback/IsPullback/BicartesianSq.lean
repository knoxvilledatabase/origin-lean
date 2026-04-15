/-
Extracted from CategoryTheory/Limits/Shapes/Pullback/IsPullback/BicartesianSq.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Bi-Cartesian squares

`BicartesianSq f g h i` is the proposition that
```
  W ---f---> X
  |          |
  g          h
  |          |
  v          v
  Y ---i---> Z

```
is a pullback square *and* a pushout square.

We show that the pullback and pushout squares for a biproduct are bi-Cartesian.
-/

noncomputable section

open CategoryTheory

open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]

structure BicartesianSq {W X Y Z : C} (f : W ⟶ X) (g : W ⟶ Y) (h : X ⟶ Z) (i : Y ⟶ Z) : Prop
    extends IsPullback f g h i, IsPushout f g h i

variable [HasZeroObject C] [HasZeroMorphisms C]

open ZeroObject

namespace IsPullback

variable {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

theorem of_hasBinaryProduct [HasBinaryProduct X Y] :
    IsPullback Limits.prod.fst Limits.prod.snd (0 : X ⟶ 0) (0 : Y ⟶ 0) := by
  convert @of_is_product _ _ X Y 0 _ (limit.isLimit _) HasZeroObject.zeroIsTerminal
    <;> subsingleton

set_option backward.isDefEq.respectTransparency false in
