/-
Extracted from CategoryTheory/Limits/Shapes/NormalMono/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Definitions and basic properties of normal monomorphisms and epimorphisms.

A normal monomorphism is a morphism that is the kernel of some other morphism.

We give the construction `NormalMono → RegularMono` (`CategoryTheory.NormalMono.regularMono`)
as well as the dual construction for normal epimorphisms. We show equivalences reflect normal
monomorphisms (`CategoryTheory.equivalenceReflectsNormalMono`), and that the pullback of a
normal monomorphism is normal (`CategoryTheory.normalOfIsPullbackSndOfNormal`).

We also define classes `IsNormalMonoCategory` and `IsNormalEpiCategory` for categories in which
every monomorphism or epimorphism is normal, and deduce that these categories are
`RegularMonoCategory`s resp. `RegularEpiCategory`s.

-/

noncomputable section

namespace CategoryTheory

open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]

variable {X Y : C}

variable [HasZeroMorphisms C]

class NormalMono (f : X ⟶ Y) where
  Z : C
  g : Y ⟶ Z
  w : f ≫ g = 0
  isLimit : IsLimit (KernelFork.ofι f w)

attribute [inherit_doc NormalMono] NormalMono.Z NormalMono.g NormalMono.w NormalMono.isLimit
