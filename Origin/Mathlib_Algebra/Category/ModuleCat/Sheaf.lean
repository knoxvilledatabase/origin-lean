/-
Extracted from Algebra/Category/ModuleCat/Sheaf.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Sheaves of modules over a sheaf of rings

In this file, we define the category `SheafOfModules R` when `R : Sheaf J RingCat`
is a sheaf of rings on a category `C` equipped with a Grothendieck topology `J`.

-/

universe v v₁ u₁ u w

open CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u})

structure SheafOfModules where
  /-- the underlying presheaf of modules of a sheaf of modules -/
  val : PresheafOfModules.{v} R.obj
  isSheaf : Presheaf.IsSheaf J val.presheaf

namespace SheafOfModules

variable {R}
