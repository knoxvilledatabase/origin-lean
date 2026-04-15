/-
Extracted from CategoryTheory/Monoidal/Closed/FunctorCategory/Complete.lean
Genuine: 1 of 5 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!

# Functors into a complete monoidal closed category form a monoidal closed category.

TODO (in progress by Joël Riou): make a more explicit construction of the internal hom in functor
categories.
-/

universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory MonoidalClosed Limits

noncomputable section

namespace CategoryTheory.Functor

variable (I : Type u₂) [Category.{v₂} I]

set_option backward.privateInPublic true in

private abbrev incl : Discrete I ⥤ I := Discrete.functor id

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C] [MonoidalClosed C]

variable [∀ (F : Discrete I ⥤ C), (Discrete.functor id).HasRightKanExtension F]

set_option backward.privateInPublic true in

set_option backward.privateInPublic.warn false in

-- INSTANCE (free from Core): :

variable [HasLimitsOfShape WalkingParallelPair C]

set_option backward.privateInPublic true in

set_option backward.privateInPublic.warn false in

-- INSTANCE (free from Core): :

set_option backward.privateInPublic true in

set_option backward.privateInPublic.warn false in

-- INSTANCE (free from Core): :

set_option backward.privateInPublic true in

set_option backward.privateInPublic.warn false in

-- INSTANCE (free from Core): (F

set_option backward.privateInPublic true in

set_option backward.privateInPublic.warn false in
