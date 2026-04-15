/-
Extracted from CategoryTheory/Limits/Shapes/Pullback/PullbackCone.lean
Genuine: 3 of 5 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# PullbackCone

This file provides API for interacting with cones (resp. cocones) in the case of pullbacks
(resp. pushouts).

## Main definitions

* `PullbackCone f g`: Given morphisms `f : X ⟶ Z` and `g : Y ⟶ Z`, a term `t : PullbackCone f g`
  provides the data of a cone pictured as follows
  ```
  t.pt ---t.snd---> Y
    |               |
  t.fst            g
    |               |
    v               v
    X -----f------> Z
  ```
  The type `PullbackCone f g` is implemented as an abbreviation for `Cone (cospan f g)`, so general
  results about cones are also available for `PullbackCone f g`.

* `PushoutCone f g`: Given morphisms `f : X ⟶ Y` and `g : X ⟶ Z`, a term `t : PushoutCone f g`
  provides the data of a cocone pictured as follows
  ```
    X -----f------> Y
    |               |
    g               t.inr
    |               |
    v               v
    Z ---t.inl---> t.pt
  ```
  Similar to `PullbackCone`, `PushoutCone f g` is implemented as an abbreviation for
  `Cocone (span f g)`, so general results about cocones are also available for `PushoutCone f g`.

## API
We summarize the most important parts of the API for pullback cones here. The dual notions for
pushout cones are also available in this file.

Various ways of constructing pullback cones:
* `PullbackCone.mk` constructs a term of `PullbackCone f g` given morphisms `fst` and `snd` such
  that `fst ≫ f = snd ≫ g`.
* `PullbackCone.flip` is the `PullbackCone` obtained by flipping `fst` and `snd`.

Interaction with `IsLimit`:
* `PullbackCone.isLimitAux` and `PullbackCone.isLimitAux'` provide two convenient ways to show that
  a given `PullbackCone` is a limit cone.
* `PullbackCone.isLimit.mk` provides a convenient way to show that a `PullbackCone` constructed
  using `PullbackCone.mk` is a limit cone.
* `PullbackCone.IsLimit.lift` and `PullbackCone.IsLimit.lift'` provides convenient ways for
  constructing the morphisms to the point of a limit `PullbackCone` from the universal property.
* `PullbackCone.IsLimit.hom_ext` provides a convenient way to show that two morphisms to the point
  of a limit `PullbackCone` are equal.

Interaction with `CommSq`:
* `CommSq.cone` and `CommSq.cocone` provide the implicit (non-limiting) pullback cone and pushout
  cocone associated with a commuting square

## References
* [Stacks: Fibre products](https://stacks.math.columbia.edu/tag/001U)
* [Stacks: Pushouts](https://stacks.math.columbia.edu/tag/0025)
-/

noncomputable section

open CategoryTheory

universe w v₁ v₂ v u u₂

namespace CategoryTheory.Limits

open WalkingSpan.Hom WalkingCospan.Hom WidePullbackShape.Hom WidePushoutShape.Hom

variable {C : Type u} [Category.{v} C] {W X Y Z : C}

abbrev PullbackCone (f : X ⟶ Z) (g : Y ⟶ Z) :=
  Cone (cospan f g)

namespace PullbackCone

variable {f : X ⟶ Z} {g : Y ⟶ Z}

abbrev fst (t : PullbackCone f g) : t.pt ⟶ X :=
  t.π.app WalkingCospan.left

abbrev snd (t : PullbackCone f g) : t.pt ⟶ Y :=
  t.π.app WalkingCospan.right
