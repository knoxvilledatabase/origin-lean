/-
Extracted from LinearAlgebra/QuadraticForm/QuadraticModuleCat/Monoidal.lean
Genuine: 2 | Conflates: 0 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core
import Mathlib.CategoryTheory.Monoidal.Transport
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.LinearAlgebra.QuadraticForm.QuadraticModuleCat
import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct.Isometries

noncomputable section

/-!
# The monoidal category structure on quadratic R-modules

The monoidal structure is simply the structure on the underlying modules, where the tensor product
of two modules is equipped with the form constructed via `QuadraticForm.tmul`.

As with the monoidal structure on `ModuleCat`,
the universe level of the modules must be at least the universe level of the ring,
so that we have a monoidal unit.
For now, we simplify by insisting both universe levels are the same.

## Implementation notes

This file essentially mirrors `Mathlib/Algebra/Category/AlgebraCat/Monoidal.lean`.
-/

open CategoryTheory

open scoped MonoidalCategory

universe v u

variable {R : Type u} [CommRing R] [Invertible (2 : R)]

namespace QuadraticModuleCat

open QuadraticMap QuadraticForm

namespace instMonoidalCategory

@[simps! form]
noncomputable abbrev tensorObj (X Y : QuadraticModuleCat.{u} R) : QuadraticModuleCat.{u} R :=
  of (X.form.tmul Y.form)

noncomputable abbrev tensorHom {W X Y Z : QuadraticModuleCat.{u} R} (f : W ⟶ X) (g : Y ⟶ Z) :
    tensorObj W Y ⟶ tensorObj X Z :=
  ⟨f.toIsometry.tmul g.toIsometry⟩

open MonoidalCategory

end instMonoidalCategory

open instMonoidalCategory

instance : MonoidalCategoryStruct (QuadraticModuleCat.{u} R) where
  tensorObj := instMonoidalCategory.tensorObj
  whiskerLeft X _ _ f := tensorHom (𝟙 X) f
  whiskerRight {X₁ X₂} (f : X₁ ⟶ X₂) Y := tensorHom f (𝟙 Y)
  tensorHom := tensorHom
  tensorUnit := of (sq (R := R))
  associator X Y Z := ofIso (tensorAssoc X.form Y.form Z.form)
  leftUnitor X := ofIso (tensorLId X.form)
  rightUnitor X := ofIso (tensorRId X.form)

@[simp] theorem toModuleCat_tensor (X Y : QuadraticModuleCat.{u} R) :
    (X ⊗ Y).toModuleCat = X.toModuleCat ⊗ Y.toModuleCat := rfl

theorem forget₂_map_associator_hom (X Y Z : QuadraticModuleCat.{u} R) :
    (forget₂ (QuadraticModuleCat R) (ModuleCat R)).map (α_ X Y Z).hom =
      (α_ X.toModuleCat Y.toModuleCat Z.toModuleCat).hom := rfl

noncomputable instance instMonoidalCategory : MonoidalCategory (QuadraticModuleCat.{u} R) :=
  Monoidal.induced
    (forget₂ (QuadraticModuleCat R) (ModuleCat R))
    { μIso := fun _ _ => Iso.refl _
      εIso := Iso.refl _
      leftUnitor_eq := fun X => by
        simp only [forget₂_obj, forget₂_map, Iso.refl_symm, Iso.trans_assoc, Iso.trans_hom,
          Iso.refl_hom, MonoidalCategory.tensorIso_hom, MonoidalCategory.tensorHom_id]
        dsimp only [toModuleCat_tensor, ModuleCat.of_coe]
        erw [MonoidalCategory.id_whiskerRight]
        simp
        rfl
      rightUnitor_eq := fun X => by
        simp only [forget₂_obj, forget₂_map, Iso.refl_symm, Iso.trans_assoc, Iso.trans_hom,
          Iso.refl_hom, MonoidalCategory.tensorIso_hom, MonoidalCategory.id_tensorHom]
        dsimp only [toModuleCat_tensor, ModuleCat.of_coe]
        erw [MonoidalCategory.whiskerLeft_id]
        simp
        rfl
      associator_eq := fun X Y Z => by
        dsimp only [forget₂_obj, forget₂_map_associator_hom]
        simp only [eqToIso_refl, Iso.refl_trans, Iso.refl_symm, Iso.trans_hom,
          MonoidalCategory.tensorIso_hom, Iso.refl_hom, MonoidalCategory.tensor_id]
        dsimp only [toModuleCat_tensor, ModuleCat.of_coe]
        rw [Category.id_comp, Category.id_comp, Category.comp_id, MonoidalCategory.tensor_id,
          Category.id_comp] }

example : (forget₂ (QuadraticModuleCat R) (ModuleCat R)).Monoidal := inferInstance

end QuadraticModuleCat
