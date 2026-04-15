/-
Extracted from CategoryTheory/ObjectProperty/ColimitsClosure.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Closure of a property of objects under colimits of certain shapes

In this file, given a property `P` of objects in a category `C` and
family of categories `J : α → Type _`, we introduce the closure
`P.colimitsClosure J` of `P` under colimits of shapes `J a` for all `a : α`,
and under certain smallness assumptions, we show that it is essentially small.

(We deduce these results about the closure under colimits by dualising the
results in the file `Mathlib/CategoryTheory/ObjectProperty/LimitsClosure.lean`.)

-/

universe w w' t v' u' v u

namespace CategoryTheory.ObjectProperty

open Limits

variable {C : Type u} [Category.{v} C] (P : ObjectProperty C)
  {α : Type t} (J : α → Type u') [∀ a, Category.{v'} (J a)]

inductive colimitsClosure : ObjectProperty C
  | of_mem (X : C) (hX : P X) : colimitsClosure X
  | of_isoClosure {X Y : C} (e : X ≅ Y) (hX : colimitsClosure X) : colimitsClosure Y
  | of_colimitPresentation {X : C} {a : α} (pres : ColimitPresentation (J a) X)
      (h : ∀ j, colimitsClosure (pres.diag.obj j)) : colimitsClosure X
