/-
Extracted from CategoryTheory/Limits/Bicones.lean
Genuine: 2 of 6 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Bicones

Given a category `J`, a walking `Bicone J` is a category whose objects are the objects of `J` and
two extra vertices `Bicone.left` and `Bicone.right`. The morphisms are the morphisms of `J` and
`left ⟶ j`, `right ⟶ j` for each `j : J` such that `(· ⟶ j)` and `(· ⟶ k)` commutes with each
`f : j ⟶ k`.

Given a diagram `F : J ⥤ C` and two `Cone F`s, we can join them into a diagram `Bicone J ⥤ C` via
`biconeMk`.

This is used in `CategoryTheory.Functor.Flat`.
-/

universe v₁ u₁

noncomputable section

open CategoryTheory.Limits

namespace CategoryTheory

section Bicone

inductive Bicone (J : Type u₁)
  | left : Bicone J
  | right : Bicone J
  | diagram (val : J) : Bicone J
  deriving DecidableEq

variable (J : Type u₁)

-- INSTANCE (free from Core): :

open scoped Classical in

-- INSTANCE (free from Core): finBicone

variable [Category.{v₁} J]

inductive BiconeHom : Bicone J → Bicone J → Type max u₁ v₁
  | left_id : BiconeHom Bicone.left Bicone.left
  | right_id : BiconeHom Bicone.right Bicone.right
  | left (j : J) : BiconeHom Bicone.left (Bicone.diagram j)
  | right (j : J) : BiconeHom Bicone.right (Bicone.diagram j)
  | diagram {j k : J} (f : j ⟶ k) : BiconeHom (Bicone.diagram j) (Bicone.diagram k)

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): BiconeHom.decidableEq
