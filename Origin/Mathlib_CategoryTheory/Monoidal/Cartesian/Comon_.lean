/-
Extracted from CategoryTheory/Monoidal/Cartesian/Comon_.lean
Genuine: 5 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.CategoryTheory.Monoidal.Comon_
import Mathlib.CategoryTheory.Monoidal.OfHasFiniteProducts

/-!
# Comonoid objects in a cartesian monoidal category.

The category of comonoid objects in a cartesian monoidal category is equivalent
to the category itself, via the forgetful functor.
-/

open CategoryTheory MonoidalCategory Limits

universe v u

noncomputable section

variable (C : Type u) [Category.{v} C] [HasTerminal C] [HasBinaryProducts C]

attribute [local instance] monoidalOfHasFiniteProducts

open monoidalOfHasFiniteProducts

attribute [local simp] associator_hom associator_inv

def cartesianComon_ : C ⥤ Comon_ C where
  obj := fun X =>
  { X := X
    comul := diag X
    counit := terminal.from X }
  map := fun f => { hom := f }

variable {C}

@[simp] theorem counit_eq_from (A : Comon_ C) : A.counit = terminal.from A.X := by ext

@[simp] theorem comul_eq_diag (A : Comon_ C) : A.comul = diag A.X := by
  ext
  · simpa using A.comul_counit =≫ prod.fst
  · simpa using A.counit_comul =≫ prod.snd

@[simps] def iso_cartesianComon_ (A : Comon_ C) : A ≅ (cartesianComon_ C).obj A.X :=
  { hom := { hom := 𝟙 _ }
    inv := { hom := 𝟙 _ } }

@[simps] def comonEquiv : Comon_ C ≌ C where
  functor := Comon_.forget C
  inverse := cartesianComon_ C
  unitIso := NatIso.ofComponents (fun A => iso_cartesianComon_ A)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _)
