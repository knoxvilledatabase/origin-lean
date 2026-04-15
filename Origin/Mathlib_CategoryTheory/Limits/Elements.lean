/-
Extracted from CategoryTheory/Limits/Elements.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Limits in the category of elements

We show that if `C` has limits of shape `I` and `A : C ⥤ Type w` preserves limits of shape `I`, then
the category of elements of `A` has limits of shape `I` and the forgetful functor
`π : A.Elements ⥤ C` creates them.

## Further results

- If `A` is (co)representable, then `A.Elements` has an initial object.

## TODOs

- Show that `A` is (co)representable if `A.Elements` has an initial object.

-/

universe w v₁ v u₁ u

namespace CategoryTheory

open Limits Opposite ConcreteCategory

variable {C : Type u} [Category.{v} C]

namespace CategoryOfElements

variable {A : C ⥤ Type w} {I : Type u₁} [Category.{v₁} I] [Small.{w} I]

namespace CreatesLimitsAux

variable (F : I ⥤ A.Elements)

set_option backward.isDefEq.respectTransparency false in

noncomputable def liftedConeElement' : limit ((F ⋙ π A) ⋙ A) :=
  Types.Limit.mk _ (fun i => (F.obj i).2) (by simp)
