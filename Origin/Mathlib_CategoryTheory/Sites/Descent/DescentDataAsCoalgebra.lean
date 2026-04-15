/-
Extracted from CategoryTheory/Sites/Descent/DescentDataAsCoalgebra.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Descent data as coalgebras

Let `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Adj Cat` be a pseudofunctor
to the bicategory of adjunctions in `Cat`. In particular,
for any morphism `g : X ⟶ Y` in `C`, we have an
adjunction `(g^*, g_*)` between a pullback functor and a
pushforward functor.

In this file, given a family of morphisms `f i : X i ⟶ S` indexed
by a type `ι` in `C`, we introduce a category `F.DescentDataAsCoalgebra f`
of descent data relative to the morphisms `f i`, where the objects are
described as a family of objects `obj i` over `X i`, and the
morphisms relating them are described as morphisms
`obj i₁ ⟶ (f i₁)^* (f i₂)_* (obj i₂)`, similarly as
Eilenberg-Moore coalgebras. Indeed, when the index type `ι`
contains a unique element, we show that
`F.DescentDataAsCoalgebra (fun (i : ι) ↦ f`
identifies to the category of coalgebras for the comonad attached
to the adjunction `(F.map f.op.toLoc).adj`.

## TODO (@joelriou, @chrisflav)
* Compare `DescentDataAsCoalgebra` with `DescentData` when suitable
  pullbacks exist and certain base change morphisms are isomorphisms

-/

universe t v' v u' u

namespace CategoryTheory

open Bicategory Opposite

namespace Pseudofunctor

variable {C : Type u} [Category.{v} C]
  {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Adj Cat.{v', u'}}

variable (F) in

structure DescentDataAsCoalgebra
    {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S) where
  /-- The objects over `X i` for all `i` -/
  obj (i : ι) : (F.obj (.mk (op (X i)))).obj
  /-- The compatibility morphisms. -/
  hom (i₁ i₂ : ι) : obj i₁ ⟶
    (F.map (f i₁).op.toLoc).l.toFunctor.obj
      ((F.map (f i₂).op.toLoc).r.toFunctor.obj (obj i₂))
  counit (i : ι) : hom i i ≫ (F.map (f i).op.toLoc).adj.counit.toNatTrans.app _ = 𝟙 _ :=
    by cat_disch
  coassoc (i₁ i₂ i₃ : ι) :
    hom i₁ i₂ ≫ (F.map (f i₁).op.toLoc).l.toFunctor.map
      ((F.map (f i₂).op.toLoc).r.toFunctor.map (hom i₂ i₃)) =
    hom i₁ i₃ ≫
      (F.map (f i₁).op.toLoc).l.toFunctor.map
        ((F.map (f i₂).op.toLoc).adj.unit.toNatTrans.app _) := by cat_disch

namespace DescentDataAsCoalgebra

attribute [reassoc (attr := simp)] counit coassoc

variable {ι : Type t} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}
