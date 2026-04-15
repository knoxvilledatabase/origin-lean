/-
Extracted from AlgebraicTopology/SimplicialSet/Op.lean
Genuine: 3 of 5 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# The covariant involution of the category of simplicial sets

In this file, we define the covariant involution `opFunctor : SSet ⥤ SSet`
of the category of simplicial sets that is induced by the
covariant involution `SimplexCategory.op : SimplexCategory ⥤ SimplexCategory`.
We use an abbreviation `X.op` for `opFunctor.obj X`.


## TODO

* Show that this involution sends `Δ[n]` to itself, and that via
  this identification, the horn `horn n i` is sent to `horn n i.rev` (@joelriou)
* Construct an isomorphism `nerve Cᵒᵖ ≅ (nerve C).op` (@robin-carlier)
* Show that the topological realization of `X.op` identifies to the
  topological realization of `X` (@joelriou)

-/

universe u

open CategoryTheory Simplicial

namespace SSet

def opFunctor : SSet.{u} ⥤ SSet.{u} := SimplicialObject.opFunctor

protected abbrev op (X : SSet.{u}) : SSet.{u} := opFunctor.obj X

def opObjEquiv {X : SSet.{u}} {n : SimplexCategoryᵒᵖ} :
    X.op.obj n ≃ X.obj n := Equiv.refl _

set_option backward.isDefEq.respectTransparency false in
