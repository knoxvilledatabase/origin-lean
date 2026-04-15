/-
Extracted from CategoryTheory/Limits/Shapes/Pullback/IsPullback/Defs.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Pullback and pushout squares

We provide another API for pullbacks and pushouts.

`IsPullback fst snd f g` is the proposition that
```
  P --fst--> X
  |          |
 snd         f
  |          |
  v          v
  Y ---g---> Z

```
is a pullback square.

(And similarly for `IsPushout`.)

We provide the glue to go back and forth to the usual `IsLimit` API for pullbacks, and prove
`IsPullback (pullback.fst f g) (pullback.snd f g) f g`
for the usual `pullback f g` provided by the `HasLimit` API.
-/

noncomputable section

open CategoryTheory

open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]

structure IsPullback {P X Y Z : C} (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z) : Prop
    extends CommSq fst snd f g where
  /-- the pullback cone is a limit -/
  isLimit' : Nonempty (IsLimit (PullbackCone.mk _ _ w))

structure IsPushout {Z X Y P : C} (f : Z ⟶ X) (g : Z ⟶ Y) (inl : X ⟶ P) (inr : Y ⟶ P) : Prop
    extends CommSq f g inl inr where
  /-- the pushout cocone is a colimit -/
  isColimit' : Nonempty (IsColimit (PushoutCocone.mk _ _ w))

namespace IsPullback

variable {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

def cone (h : IsPullback fst snd f g) : PullbackCone f g :=
  h.toCommSq.cone
