/-
Extracted from CategoryTheory/Presentable/LocallyPresentable.lean
Genuine: 4 of 5 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Locally presentable and accessible categories

In this file, we define the notion of locally presentable and accessible
categories. We first define these notions for a category `C` relative to a
fixed regular cardinal `κ` (typeclasses `IsCardinalLocallyPresentable C κ`
and `IsCardinalAccessibleCategory C κ`). The existence of such a regular
cardinal `κ` is asserted in the typeclasses `IsLocallyPresentable` and
`IsAccessibleCategory`. We show that in a locally presentable or
accessible category, any object is presentable.

## References
* [Adámek, J. and Rosický, J., *Locally presentable and accessible categories*][Adamek_Rosicky_1994]

-/

universe w v u

namespace CategoryTheory

open Limits

variable (C : Type u) [Category.{v} C] (κ : Cardinal.{w}) [Fact κ.IsRegular]

class IsCardinalLocallyPresentable : Prop
  extends HasCardinalFilteredGenerator C κ, HasColimitsOfSize.{w, w} C where

example (κ : Cardinal.{w}) [Fact κ.IsRegular] [IsCardinalLocallyPresentable C κ] :

    ObjectProperty.EssentiallySmall.{w} (isCardinalPresentable C κ) := inferInstance

class IsCardinalAccessibleCategory : Prop
  extends HasCardinalFilteredGenerator C κ, HasCardinalFilteredColimits.{w} C κ where

-- INSTANCE (free from Core): [IsCardinalLocallyPresentable

example (κ : Cardinal.{w}) [Fact κ.IsRegular] [IsCardinalAccessibleCategory C κ] :

    ObjectProperty.EssentiallySmall.{w} (isCardinalPresentable C κ) := inferInstance

section Finite

open Cardinal

attribute [local instance] fact_isRegular_aleph0

abbrev IsLocallyFinitelyPresentable :=
  IsCardinalLocallyPresentable.{w} C ℵ₀

abbrev IsFinitelyAccessibleCategory :=
  IsCardinalAccessibleCategory.{w} C ℵ₀

end Finite

end
