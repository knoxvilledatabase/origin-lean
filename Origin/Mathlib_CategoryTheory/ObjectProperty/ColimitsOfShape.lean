/-
Extracted from CategoryTheory/ObjectProperty/ColimitsOfShape.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Objects that are colimits of objects satisfying a certain property

Given a property of objects `P : ObjectProperty C` and a category `J`,
we introduce two properties of objects `P.strictColimitsOfShape J`
and `P.colimitsOfShape J`. The former contains exactly the objects
of the form `colimit F` for any functor `F : J ⥤ C` that has
a colimit and such that `F.obj j` satisfies `P` for any `j`, while
the latter contains all the objects that are isomorphic to
these "chosen" objects `colimit F`.

Under certain circumstances, the type of objects satisfying
`P.strictColimitsOfShape J` is small: the main reason this variant is
introduced is to deduce that the full subcategory of `P.colimitsOfShape J`
is essentially small.

By requiring `P.colimitsOfShape J ≤ P`, we introduce a typeclass
`P.IsClosedUnderColimitsOfShape J`.

We also show that `colimitsOfShape` in a category `C` is related
to `limitsOfShape` in the opposite category `Cᵒᵖ` and vice versa.

## TODO

* refactor `ObjectProperty.ind` by saying that it is the supremum
  of `P.colimitsOfShape J` for a filtered category `J`
  (generalize also to `κ`-filtered categories?)
* formalize the closure of `P` under finite colimits (which require
  iterating over `ℕ`), and more generally the closure under colimits
  indexed by a category whose type of arrows has a cardinality
  that is bounded by a certain regular cardinal (@joelriou)

-/

universe w v'' v' u'' u' v u

namespace CategoryTheory.ObjectProperty

open Limits

variable {C D : Type*} [Category* C] [Category* D] (P : ObjectProperty C)
  (J : Type u') [Category.{v'} J]
  {J' : Type u''} [Category.{v''} J']

inductive strictColimitsOfShape : ObjectProperty C
  | colimit (F : J ⥤ C) [HasColimit F] (hF : ∀ j, P (F.obj j)) :
    strictColimitsOfShape (colimit F)

variable {P} in

lemma strictColimitsOfShape_monotone {Q : ObjectProperty C} (h : P ≤ Q) :
    P.strictColimitsOfShape J ≤ Q.strictColimitsOfShape J := by
  rintro _ ⟨F, hF⟩
  exact ⟨F, fun j ↦ h _ (hF j)⟩
