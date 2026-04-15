/-
Extracted from CategoryTheory/Products/Unitor.lean
Genuine: 6 of 8 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.DiscreteCategory

/-!
# The left/right unitor equivalences `1 × C ≌ C` and `C × 1 ≌ C`.
-/

universe w v u

open CategoryTheory

namespace CategoryTheory.prod

variable (C : Type u) [Category.{v} C]

@[simps]
def leftUnitor : Discrete (PUnit : Type w) × C ⥤ C where
  obj X := X.2
  map f := f.2

@[simps]
def rightUnitor : C × Discrete (PUnit : Type w) ⥤ C where
  obj X := X.1
  map f := f.1

@[simps]
def leftInverseUnitor : C ⥤ Discrete (PUnit : Type w) × C where
  obj X := ⟨⟨PUnit.unit⟩, X⟩
  map f := ⟨𝟙 _, f⟩

@[simps]
def rightInverseUnitor : C ⥤ C × Discrete (PUnit : Type w) where
  obj X := ⟨X, ⟨PUnit.unit⟩⟩
  map f := ⟨f, 𝟙 _⟩

@[simps]
def leftUnitorEquivalence : Discrete (PUnit : Type w) × C ≌ C where
  functor := leftUnitor C
  inverse := leftInverseUnitor C
  unitIso := Iso.refl _
  counitIso := Iso.refl _

@[simps]
def rightUnitorEquivalence : C × Discrete (PUnit : Type w) ≌ C where
  functor := rightUnitor C
  inverse := rightInverseUnitor C
  unitIso := Iso.refl _
  counitIso := Iso.refl _

instance leftUnitor_isEquivalence : (leftUnitor C).IsEquivalence :=
  (leftUnitorEquivalence C).isEquivalence_functor

instance rightUnitor_isEquivalence : (rightUnitor C).IsEquivalence :=
  (rightUnitorEquivalence C).isEquivalence_functor

end CategoryTheory.prod
