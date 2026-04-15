/-
Extracted from CategoryTheory/Limits/Shapes/Pullback/HasPullback.lean
Genuine: 16 of 16 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# HasPullback
`HasPullback f g` and `pullback f g` provides API for `HasLimit` and `limit` in the case of
pullbacks.

## Main definitions

* `HasPullback f g`: this is an abbreviation for `HasLimit (cospan f g)`, and is a typeclass used to
  express the fact that a given pair of morphisms has a pullback.

* `HasPullbacks`: expresses the fact that `C` admits all pullbacks, it is implemented as an
  abbreviation for `HasLimitsOfShape WalkingCospan C`

* `pullback f g`: Given a `HasPullback f g` instance, this function returns the choice of a limit
  object corresponding to the pullback of `f` and `g`. It fits into the following diagram:
  ```
    pullback f g ---pullback.fst f g---> X
        |                                |
        |                                |
  pullback.snd f g                       f
        |                                |
        v                                v
        Y --------------g--------------> Z
  ```

* `HasPushout f g`: this is an abbreviation for `HasColimit (span f g)`, and is a typeclass used to
  express the fact that a given pair of morphisms has a pushout.
* `HasPushouts`: expresses the fact that `C` admits all pushouts, it is implemented as an
  abbreviation for `HasColimitsOfShape WalkingSpan C`
* `pushout f g`: Given a `HasPushout f g` instance, this function returns the choice of a colimit
  object corresponding to the pushout of `f` and `g`. It fits into the following diagram:
  ```
      X --------------f--------------> Y
      |                                |
      g                          pushout.inl f g
      |                                |
      v                                v
      Z ---pushout.inr f g---> pushout f g
  ```

## Main results & API
* The following API is available for using the universal property of `pullback f g`:
  `lift`, `lift_fst`, `lift_snd`, `lift'`, `hom_ext` (for uniqueness).

* `pullback.map` is the induced map between pullbacks `W ×ₛ X ⟶ Y ×ₜ Z` given pointwise
  (compatible) maps `W ⟶ Y`, `X ⟶ Z` and `S ⟶ T`.

* `pullbackComparison`: Given a functor `G`, this is the natural morphism
  `G.obj (pullback f g) ⟶ pullback (G.map f) (G.map g)`

* `pullbackSymmetry` provides the natural isomorphism `pullback f g ≅ pullback g f`

(The dual results for pushouts are also available)

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

abbrev HasPullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :=
  HasLimit (cospan f g)

abbrev HasPushout {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :=
  HasColimit (span f g)

abbrev pullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :=
  limit (cospan f g)

abbrev pullback.cone {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] : PullbackCone f g :=
  limit.cone (cospan f g)

abbrev pushout {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] :=
  colimit (span f g)

abbrev pushout.cocone {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] : PushoutCocone f g :=
  colimit.cocone (span f g)

abbrev pullback.fst {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] : pullback f g ⟶ X :=
  limit.π (cospan f g) WalkingCospan.left

abbrev pullback.snd {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] : pullback f g ⟶ Y :=
  limit.π (cospan f g) WalkingCospan.right

abbrev pushout.inl {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] : Y ⟶ pushout f g :=
  colimit.ι (span f g) WalkingSpan.left

abbrev pushout.inr {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] : Z ⟶ pushout f g :=
  colimit.ι (span f g) WalkingSpan.right

abbrev pullback.lift {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] (h : W ⟶ X)
    (k : W ⟶ Y) (w : h ≫ f = k ≫ g := by cat_disch) : W ⟶ pullback f g :=
  limit.lift _ (PullbackCone.mk h k w)

set_option backward.isDefEq.respectTransparency false in

lemma pullback.exists_lift {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
    (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g := by cat_disch) :
    ∃ (l : W ⟶ pullback f g), l ≫ pullback.fst f g = h ∧ l ≫ pullback.snd f g = k :=
  ⟨pullback.lift h k, by simp⟩

abbrev pushout.desc {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] (h : Y ⟶ W) (k : Z ⟶ W)
    (w : f ≫ h = g ≫ k := by cat_disch) : pushout f g ⟶ W :=
  colimit.desc _ (PushoutCocone.mk h k w)

set_option backward.isDefEq.respectTransparency false in

lemma pushout.exists_desc {W X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g]
    (h : Y ⟶ W) (k : Z ⟶ W) (w : f ≫ h = g ≫ k := by cat_disch) :
    ∃ (l : pushout f g ⟶ W), pushout.inl f g ≫ l = h ∧ pushout.inr f g ≫ l = k :=
  ⟨pushout.desc h k, by simp⟩

abbrev pullback.isLimit {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :
    IsLimit (pullback.cone f g) :=
  limit.isLimit (cospan f g)

abbrev pushout.isColimit {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] :
    IsColimit (pushout.cocone f g) :=
  colimit.isColimit (span f g)
