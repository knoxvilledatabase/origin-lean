/-
Extracted from Algebra/Homology/Monoidal.lean
Genuine: 9 of 14 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-!
# The monoidal category structure on homological complexes

Let `c : ComplexShape I` with `I` an additive monoid. If `c` is equipped
with the data and axioms `c.TensorSigns`, then the category
`HomologicalComplex C c` can be equipped with a monoidal category
structure if `C` is a monoidal category such that `C` has certain
coproducts and both left/right tensoring commute with these.

In particular, we obtain a monoidal category structure on
`ChainComplex C ℕ` when `C` is an additive monoidal category.

-/

assert_not_exists TwoSidedIdeal

open CategoryTheory Limits MonoidalCategory Category

namespace HomologicalComplex

variable {C : Type*} [Category* C] [MonoidalCategory C] [Preadditive C] [HasZeroObject C]
  [(curriedTensor C).Additive] [∀ (X₁ : C), ((curriedTensor C).obj X₁).Additive]
  {I : Type*} [AddMonoid I] {c : ComplexShape I} [c.TensorSigns]

abbrev HasTensor (K₁ K₂ : HomologicalComplex C c) := HasMapBifunctor K₁ K₂ (curriedTensor C) c

variable [DecidableEq I]

noncomputable abbrev tensorObj (K₁ K₂ : HomologicalComplex C c) [HasTensor K₁ K₂] :
    HomologicalComplex C c :=
  mapBifunctor K₁ K₂ (curriedTensor C) c

noncomputable abbrev ιTensorObj (K₁ K₂ : HomologicalComplex C c) [HasTensor K₁ K₂]
    (i₁ i₂ j : I) (h : i₁ + i₂ = j) :
    K₁.X i₁ ⊗ K₂.X i₂ ⟶ (tensorObj K₁ K₂).X j :=
  ιMapBifunctor K₁ K₂ (curriedTensor C) c i₁ i₂ j h

noncomputable abbrev tensorHom {K₁ K₂ L₁ L₂ : HomologicalComplex C c}
    (f : K₁ ⟶ L₁) (g : K₂ ⟶ L₂) [HasTensor K₁ K₂] [HasTensor L₁ L₂] :
    tensorObj K₁ K₂ ⟶ tensorObj L₁ L₂ :=
  mapBifunctorMap f g _ _

abbrev HasGoodTensor₁₂ (K₁ K₂ K₃ : HomologicalComplex C c) :=
  HasGoodTrifunctor₁₂Obj (curriedTensor C) (curriedTensor C) K₁ K₂ K₃ c c

abbrev HasGoodTensor₂₃ (K₁ K₂ K₃ : HomologicalComplex C c) :=
  HasGoodTrifunctor₂₃Obj (curriedTensor C) (curriedTensor C) K₁ K₂ K₃ c c c

noncomputable abbrev associator (K₁ K₂ K₃ : HomologicalComplex C c)
    [HasTensor K₁ K₂] [HasTensor K₂ K₃]
    [HasTensor (tensorObj K₁ K₂) K₃] [HasTensor K₁ (tensorObj K₂ K₃)]
    [HasGoodTensor₁₂ K₁ K₂ K₃] [HasGoodTensor₂₃ K₁ K₂ K₃] :
    tensorObj (tensorObj K₁ K₂) K₃ ≅ tensorObj K₁ (tensorObj K₂ K₃) :=
  mapBifunctorAssociator (curriedAssociatorNatIso C) K₁ K₂ K₃ c c c

variable (C c) in

noncomputable abbrev tensorUnit : HomologicalComplex C c := (single C c 0).obj (𝟙_ C)

variable (C c) in

noncomputable def tensorUnitIso :
    (GradedObject.single₀ I).obj (𝟙_ C) ≅ (tensorUnit C c).X :=
  GradedObject.isoMk _ _ (fun i ↦
    if hi : i = 0 then
      (GradedObject.singleObjApplyIsoOfEq (0 : I) (𝟙_ C) i hi).trans
        (singleObjXIsoOfEq c 0 (𝟙_ C) i hi).symm
    else
      { hom := 0
        inv := 0
        hom_inv_id := (GradedObject.isInitialSingleObjApply 0 (𝟙_ C) i hi).hom_ext _ _
        inv_hom_id := (isZero_single_obj_X c 0 (𝟙_ C) i hi).eq_of_src _ _ })

end

-- INSTANCE (free from Core): (K₁

-- INSTANCE (free from Core): (K₁

-- INSTANCE (free from Core): (K₁

variable (K : HomologicalComplex C c) [DecidableEq I]

variable [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :
