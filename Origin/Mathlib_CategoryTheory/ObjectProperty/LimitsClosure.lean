/-
Extracted from CategoryTheory/ObjectProperty/LimitsClosure.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Closure of a property of objects under limits of certain shapes

In this file, given a property `P` of objects in a category `C` and
a family of categories `J : α → Type _`, we introduce the closure
`P.limitsClosure J` of `P` under limits of shapes `J a` for all `a : α`,
and under certain smallness assumptions, we show that it is essentially small.

-/

universe w w' t v' u' v u

namespace CategoryTheory.ObjectProperty

open Limits

variable {C : Type u} [Category.{v} C] (P : ObjectProperty C)
  {α : Type t} (J : α → Type u') [∀ a, Category.{v'} (J a)]

inductive limitsClosure : ObjectProperty C
  | of_mem (X : C) (hX : P X) : limitsClosure X
  | of_isoClosure {X Y : C} (e : X ≅ Y) (hX : limitsClosure X) : limitsClosure Y
  | of_limitPresentation {X : C} {a : α} (pres : LimitPresentation (J a) X)
      (h : ∀ j, limitsClosure (pres.diag.obj j)) : limitsClosure X
