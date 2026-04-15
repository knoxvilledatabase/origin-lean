/-
Extracted from CategoryTheory/Monoidal/Cartesian/Comon_.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Comonoid objects in a Cartesian monoidal category.

The category of comonoid objects in a Cartesian monoidal category is equivalent
to the category itself, via the forgetful functor.
-/

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Limits ComonObj

universe v u

noncomputable section

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] [CartesianMonoidalCategory C]

attribute [local simp] leftUnitor_hom rightUnitor_hom

def cartesianComon : C ⥤ Comon C where
  obj X := {
    X := X
    comon := {
      comul := lift (𝟙 _) (𝟙 _)
      counit := toUnit _
    }
  }
  map f := .mk' f (f_comul := by
    #adaptation_note /-- Prior to https://github.com/leanprover/lean4/pull/12244
    this argument was provided by the auto_param. -/
    simp +instances)

variable {C}
