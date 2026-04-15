/-
Extracted from Geometry/RingedSpace/Stalks.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Stalks for presheafed spaces

This file lifts constructions of stalks and pushforwards of stalks to work with
the category of presheafed spaces. Additionally, we prove that restriction of
presheafed spaces does not change the stalks.
-/

noncomputable section

universe v u v' u'

open Opposite CategoryTheory CategoryTheory.Category CategoryTheory.Functor CategoryTheory.Limits

  AlgebraicGeometry TopologicalSpace Topology

variable {C : Type u} [Category.{v} C] [HasColimits C]

attribute [local aesop safe cases (rule_sets := [CategoryTheory])] Opens

open TopCat.Presheaf

namespace AlgebraicGeometry.PresheafedSpace

def Hom.stalkMap {X Y : PresheafedSpace.{_, _, v} C} (α : Hom X Y) (x : X) :
    Y.presheaf.stalk (α.base x) ⟶ X.presheaf.stalk x :=
  (stalkFunctor C (α.base x)).map α.c ≫ X.presheaf.stalkPushforward C α.base x

set_option backward.isDefEq.respectTransparency false in
