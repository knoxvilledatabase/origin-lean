/-
Extracted from CategoryTheory/Sites/Point/Basic.lean
Genuine: 3 of 6 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Points of a site

Let `C` be a category equipped with a Grothendieck topology `J`. In this file,
we define the notion of point of the site `(C, J)`, as a
structure `GrothendieckTopology.Point`. Such a `Φ : J.Point` consists
in a functor `Φ.fiber : C ⥤ Type w` such that the category `Φ.fiber.Elements`
is cofiltered (and initially small) and such that if `x : Φ.fiber.obj X`
and `R` is a covering sieve of `X`, then `x` belongs to the image
of some `y : Φ.fiber.obj Y` by a morphism `f : Y ⟶ X` which belongs to `R`.
(This definition is essentially the definition of a fiber functor on a site
from SGA 4 IV 6.3.)

The fact that `Φ.fiber.Elementsᵒᵖ` is filtered allows to define
`Φ.presheafFiber : (Cᵒᵖ ⥤ A) ⥤ A` by taking the filtering colimit
of the evaluation functors at `op X` when `(X : C, x : F.obj X)` varies in
`Φ.fiber.Elementsᵒᵖ`. We define `Φ.sheafFiber : Sheaf J A ⥤ A` as the
restriction of `Φ.presheafFiber` to the full subcategory of sheaves.

Under certain assumptions, we show that if `A` is concrete and
`P ⟶ Q` is a locally bijective morphism between presheaves,
then the induced morphism on fibers is a bijection. It follows
that not only `Φ.sheafFiber : Sheaf J A ⥤ A` is the restriction of
`Φ.presheafFiber` but it may also be thought as a localization
of this functor with respect to the class of morphisms `J.W`.
In particular, the fiber of a presheaf identifies to the fiber of
its associated sheaf.

Under suitable assumptions on the target category `A`, we show that
both `Φ.presheafFiber` and `Φ.sheafFiber` commute with finite limits
and with arbitrary colimits. (The commutation of `Φ.sheafFiber` with colimits
is obtained in the file `Mathlib/CategoryTheory/Sites/Point/Skyscraper.lean`.)

-/

universe w' w v v' v'' u u' u''

namespace CategoryTheory

open Limits Opposite

variable {C : Type u} [Category.{v} C]

namespace GrothendieckTopology

variable (J : GrothendieckTopology C)

structure Point where
  /-- the fiber functor on the underlying category of the site -/
  fiber : C ⥤ Type w
  isCofiltered : IsCofiltered fiber.Elements := by infer_instance
  initiallySmall : InitiallySmall.{w} fiber.Elements := by infer_instance
  jointly_surjective {X : C} (R : Sieve X) (h : R ∈ J X) (x : fiber.obj X) :
    ∃ (Y : C) (f : Y ⟶ X) (_ : R f) (y : fiber.obj Y), fiber.map f y = x

namespace Point

attribute [instance] initiallySmall isCofiltered

variable {J} (Φ : Point.{w} J) {A : Type u'} [Category.{v'} A]
  {B : Type u''} [Category.{v''} B]
  [HasColimitsOfSize.{w, w} A] [HasColimitsOfSize.{w, w} B]

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): [LocallySmall.{w}

noncomputable def presheafFiber : (Cᵒᵖ ⥤ A) ⥤ A :=
  (Functor.whiskeringLeft _ _ _).obj (CategoryOfElements.π Φ.fiber).op ⋙ colim

noncomputable def toPresheafFiber (X : C) (x : Φ.fiber.obj X) (P : Cᵒᵖ ⥤ A) :
    P.obj (op X) ⟶ Φ.presheafFiber.obj P :=
  colimit.ι ((CategoryOfElements.π Φ.fiber).op ⋙ P) (op ⟨X, x⟩)
