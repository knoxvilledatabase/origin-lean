/-
Extracted from CategoryTheory/Limits/Types/ColimitType.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The colimit type of a functor to types

Given a category `J` (with `J : Type u` and `[Category.{v} J]`) and
a functor `F : J ⥤ Type w₀`, we introduce a type `F.ColimitType : Type (max u w₀)`,
which satisfies a certain universal property of the colimit: it is defined
as a suitable quotient of `Σ j, F.obj j`. This universal property is not
expressed in a categorical way (as in general `Type (max u w₀)`
is not the same as `Type u`).

We also introduce a notion of cocone of `F : J ⥤ Type w₀`, this is `F.CoconeTypes`,
or more precisely `Functor.CoconeTypes.{w₁} F`, which consists of a candidate
colimit type for `F` which is in `Type w₁` (in case `w₁ = w₀`, we shall show
this is the same as the data of `c : Cocone F` in the categorical sense).
Given `c : F.CoconeTypes`, we also introduce a property `c.IsColimit` which says
that the canonical map `F.ColimitType → c.pt` is a bijection, and we shall show (TODO)
that when `w₁ = w₀`, it is equivalent to saying that the corresponding cocone
in a categorical sense is a colimit.

## TODO
* refactor `DirectedSystem` and the construction of colimits in `Type`
  by using `Functor.ColimitType`.
* add a similar API for limits in `Type`?

-/

universe w₃ w₂ w₁ w₀ w₀' v u

assert_not_exists CategoryTheory.Limits.Cocone

namespace CategoryTheory

variable {J : Type u} [Category.{v} J]

namespace Functor

variable (F : J ⥤ Type w₀)

structure CoconeTypes where
  /-- the point of the cocone -/
  pt : Type w₁
  /-- a family of maps to `pt` -/
  ι (j : J) : F.obj j → pt
  ι_naturality {j j' : J} (f : j ⟶ j') :
      (ι j').comp (F.map f) = ι j := by aesop

namespace CoconeTypes

attribute [simp] ι_naturality

variable {F}
