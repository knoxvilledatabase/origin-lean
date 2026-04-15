/-
Extracted from Algebra/Category/ModuleCat/Presheaf/ColimitFunctor.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The colimit module of a presheaf of modules on a cofiltered category

Given a colimit cocone `cR` for a presheaf of rings `R` on a cofiltered category `C`,
`M` a presheaf of modules over `R`, and a colimit cocone `cM` for the underlying
functor `Cᵒᵖ ⥤ AddCommGrpCat` of `M`, we define a structure of module over `cR.pt`
on a type-synonym `PresheafOfModules.ModuleColimit` for `cM.pt`. This extends to
a functor `PresheafOfModules.colimitFunctor : PresheafOfModules R ⥤ ModuleCat cR.pt`.

## TODO (@joelriou)
* Define fiber functors on categories of (pre)sheaves of modules
* Refactor `Mathlib/Algebra/Category/ModuleCat/Stalk.lean` so that it uses
this slightly more general construction.

-/

universe w v u

open CategoryTheory Limits MonoidalCategory

attribute [local instance] hasColimitsOfShape_of_finallySmall

  IsFiltered.isSifted FinallySmall.preservesColimitsOfShape_of_isFiltered

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C]
  [IsCofiltered C] [InitiallySmall.{w} C]
  {R : Cᵒᵖ ⥤ RingCat.{w}} {cR : Cocone R} (hcR : IsColimit cR)

variable (cR) in

noncomputable def constFunctor : ModuleCat cR.pt ⥤ PresheafOfModules.{w} R where
  obj M :=
    { obj X := (ModuleCat.restrictScalars (cR.ι.app X).hom).obj M
      map {X Y} f :=
        (ModuleCat.restrictScalarsComp' _ _ _
          (by ext; dsimp; rw [← Cocone.w cR f]; dsimp; rfl)).hom.app _ }
  map φ := { app X := (ModuleCat.restrictScalars (cR.ι.app X).hom).map φ }

variable {M : PresheafOfModules.{w} R} {cM : Cocone M.presheaf} (hcM : IsColimit cM)
  {M' : PresheafOfModules.{w} R} {cM' : Cocone M'.presheaf} (hcM' : IsColimit cM')
  {M'' : PresheafOfModules.{w} R} {cM'' : Cocone M''.presheaf} (hcM'' : IsColimit cM'')
