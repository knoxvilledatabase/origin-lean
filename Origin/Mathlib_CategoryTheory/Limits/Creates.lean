/-
Extracted from CategoryTheory/Limits/Creates.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Creating (co)limits

We say that `F` creates limits of `K` if, given any limit cone `c` for `K ⋙ F`
(i.e. below), we can lift it to a cone "above", and further that `F` reflects
limits for `K`.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

noncomputable section

namespace CategoryTheory

universe w' w'₁ w w₁ v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C]

section Creates

variable {D : Type u₂} [Category.{v₂} D]

variable {J : Type w} [Category.{w'} J] {K : J ⥤ C}

structure LiftableCone (K : J ⥤ C) (F : C ⥤ D) (c : Cone (K ⋙ F)) where
  /-- a cone in the source category of the functor -/
  liftedCone : Cone K
  /-- the isomorphism expressing that `liftedCone` lifts the given cone -/
  validLift : F.mapCone liftedCone ≅ c

structure LiftableCocone (K : J ⥤ C) (F : C ⥤ D) (c : Cocone (K ⋙ F)) where
  /-- a cocone in the source category of the functor -/
  liftedCocone : Cocone K
  /-- the isomorphism expressing that `liftedCocone` lifts the given cocone -/
  validLift : F.mapCocone liftedCocone ≅ c

class CreatesLimit (K : J ⥤ C) (F : C ⥤ D) extends ReflectsLimit K F where
  /-- any limit cone can be lifted to a cone above -/
  lifts : ∀ c, IsLimit c → LiftableCone K F c

class CreatesLimitsOfShape (J : Type w) [Category.{w'} J] (F : C ⥤ D) where
  CreatesLimit : ∀ {K : J ⥤ C}, CreatesLimit K F := by infer_instance
