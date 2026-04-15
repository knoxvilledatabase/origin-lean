/-
Extracted from CategoryTheory/Presentable/Basic.lean
Genuine: 5 of 9 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-! # Presentable objects

A functor `F : C ⥤ D` is `κ`-accessible (`Functor.IsCardinalAccessible`)
if it commutes with colimits of shape `J` where `J` is any `κ`-filtered category
(that is essentially small relative to the universe `w` such that `κ : Cardinal.{w}`.).
We also introduce another typeclass `Functor.IsAccessible` saying that there exists
a regular cardinal `κ` such that `Functor.IsCardinalAccessible`.

An object `X` of a category is `κ`-presentable (`IsCardinalPresentable`)
if the functor `Hom(X, _)` (i.e. `coyoneda.obj (op X)`) is `κ`-accessible.
Similarly as for accessible functors, we define a type class `IsAccessible`.

## References
* [Adámek, J. and Rosický, J., *Locally presentable and accessible categories*][Adamek_Rosicky_1994]

-/

universe t w w' v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Limits Opposite

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace Functor

variable (F G : C ⥤ D) (e : F ≅ G) (κ : Cardinal.{w}) [Fact κ.IsRegular]

class IsCardinalAccessible : Prop where
  preservesColimitOfShape (J : Type w) [SmallCategory J] [IsCardinalFiltered J κ] :
    PreservesColimitsOfShape J F := by intros; infer_instance

lemma preservesColimitsOfShape_of_isCardinalAccessible [F.IsCardinalAccessible κ]
    (J : Type w) [SmallCategory J] [IsCardinalFiltered J κ] :
    PreservesColimitsOfShape J F :=
  IsCardinalAccessible.preservesColimitOfShape κ _

lemma preservesColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall
    [F.IsCardinalAccessible κ]
    (J : Type u₃) [Category.{v₃} J] [EssentiallySmall.{w} J] [IsCardinalFiltered J κ] :
    PreservesColimitsOfShape J F := by
  have := IsCardinalFiltered.of_equivalence κ (equivSmallModel.{w} J)
  have := F.preservesColimitsOfShape_of_isCardinalAccessible κ (SmallModel.{w} J)
  exact preservesColimitsOfShape_of_equiv (equivSmallModel.{w} J).symm F

variable {κ} in

lemma isCardinalAccessible_of_le
    [F.IsCardinalAccessible κ] {κ' : Cardinal.{w}} [Fact κ'.IsRegular] (h : κ ≤ κ') :
    F.IsCardinalAccessible κ' where
  preservesColimitOfShape {J _ _} := by
    have := IsCardinalFiltered.of_le J h
    exact F.preservesColimitsOfShape_of_isCardinalAccessible κ J

include e in

variable {F G} in

lemma isCardinalAccessible_of_natIso [F.IsCardinalAccessible κ] : G.IsCardinalAccessible κ where
  preservesColimitOfShape J _ hκ := by
    have := F.preservesColimitsOfShape_of_isCardinalAccessible κ J
    exact preservesColimitsOfShape_of_natIso e

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): {E

-- INSTANCE (free from Core): [PreservesColimitsOfSize.{w,

-- INSTANCE (free from Core): (A

end

variable (F : C ⥤ D)
