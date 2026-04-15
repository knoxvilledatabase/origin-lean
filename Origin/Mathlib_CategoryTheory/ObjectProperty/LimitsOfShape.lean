/-
Extracted from CategoryTheory/ObjectProperty/LimitsOfShape.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Objects that are limits of objects satisfying a certain property

Given a property of objects `P : ObjectProperty C` and a category `J`,
we introduce two properties of objects `P.strictLimitsOfShape J`
and `P.limitsOfShape J`. The former contains exactly the objects
of the form `limit F` for any functor `F : J ⥤ C` that has
a limit and such that `F.obj j` satisfies `P` for any `j`, while
the latter contains all the objects that are isomorphic to
these "chosen" objects `limit F`.

Under certain circumstances, the type of objects satisfying
`P.strictLimitsOfShape J` is small: the main reason this variant is
introduced is to deduce that the full subcategory of `P.limitsOfShape J`
is essentially small.

By requiring `P.limitsOfShape J ≤ P`, we introduce a typeclass
`P.IsClosedUnderLimitsOfShape J`.


## TODO

* formalize the closure of `P` under finite limits (which require
  iterating over `ℕ`), and more generally the closure under limits
  indexed by a category whose type of arrows has a cardinality
  that is bounded by a certain regular cardinal (@joelriou)

-/

universe w v'' v' u'' u' v u

namespace CategoryTheory.ObjectProperty

open Limits

variable {C D : Type*} [Category* C] [Category* D] (P : ObjectProperty C)
  (J : Type u') [Category.{v'} J]
  {J' : Type u''} [Category.{v''} J']

inductive strictLimitsOfShape : ObjectProperty C
  | limit (F : J ⥤ C) [HasLimit F] (hF : ∀ j, P (F.obj j)) :
    strictLimitsOfShape (limit F)

variable {P} in

lemma strictLimitsOfShape_monotone {Q : ObjectProperty C} (h : P ≤ Q) :
    P.strictLimitsOfShape J ≤ Q.strictLimitsOfShape J := by
  rintro _ ⟨F, hF⟩
  exact ⟨F, fun j ↦ h _ (hF j)⟩
