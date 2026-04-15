/-
Extracted from CategoryTheory/Sites/Descent/IsPrestack.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Prestacks: descent of morphisms

Let `C` be a category and `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`.
Given `S : C`, and objects `M` and `N` in `F.obj (.mk (op S))`,
we define a presheaf of types `F.presheafHom M N` on the category `Over S`:
its sections on an object `T : Over S` corresponding to a morphism `p : X ⟶ S`
are the type of morphisms `p^* M ⟶ p^* N`. We shall say that
`F` satisfies the descent of morphisms for a Grothendieck topology `J`
if these presheaves are all sheaves (typeclass `F.IsPrestack J`).

## Terminological note

In this file, we use the language of pseudofunctors to formalize prestacks.
Similar notions could also be phrased in terms of fibered categories.
In the mathematical literature, various uses of the words "prestacks" and
"stacks" exists. Our definitions are consistent with Giraud's definition II 1.2.1
in *Cohomologie non abélienne*: a prestack is defined by the descent of morphisms
condition with respect to a Grothendieck topology, and a stack by the effectiveness
of the descent. However, contrary to Laumon and Moret-Bailly in *Champs algébriques* 3.1,
we do not require that target categories are groupoids.

## References
* [Jean Giraud, *Cohomologie non abélienne*][giraud1971]
* [Gérard Laumon and Laurent Moret-Bailly, *Champs algébriques*][laumon-morel-bailly-2000]

-/

universe v' v u' u

namespace CategoryTheory

open Opposite Bicategory

namespace Pseudofunctor

variable {C : Type u} [Category.{v} C] {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}

namespace LocallyDiscreteOpToCat

def pullHom ⦃X₁ X₂ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op X₂))⦄
    ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂) ⦃Y' : C⦄
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch)
    (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    (F.map gf₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map gf₂.op.toLoc).toFunctor.obj M₂ :=
  (F.mapComp' f₁.op.toLoc g.op.toLoc gf₁.op.toLoc (by aesop)).hom.toNatTrans.app _ ≫
    (F.map g.op.toLoc).toFunctor.map φ ≫
      (F.mapComp' f₂.op.toLoc g.op.toLoc gf₂.op.toLoc (by aesop)).inv.toNatTrans.app _

set_option backward.isDefEq.respectTransparency false in
