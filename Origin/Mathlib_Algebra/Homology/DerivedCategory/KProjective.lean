/-
Extracted from Algebra/Homology/DerivedCategory/KProjective.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Morphisms from K-projective complexes in the derived category

In this file, we show that if `K : CochainComplex C ℤ` is K-projective,
then for any `L : HomotopyCategory C (.up ℤ)`, the functor `DerivedCategory.Qh`
induces a bijection from the type of morphisms `(HomotopyCategory.quotient _ _).obj K) ⟶ L`
(i.e. homotopy classes of morphisms of cochain complexes) to the type of
morphisms in the derived category.

-/

universe w v u

open CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

open CategoryTheory Localization DerivedCategory

namespace CochainComplex

lemma IsKProjective.Qh_map_bijective [HasDerivedCategory C]
    (K : CochainComplex C ℤ) (L : HomotopyCategory C (ComplexShape.up ℤ))
    [K.IsKProjective] :
    Function.Bijective (DerivedCategory.Qh.map :
      ((HomotopyCategory.quotient _ _).obj K ⟶ L) → _) :=
  (CochainComplex.IsKProjective.leftOrthogonal K).map_bijective_of_isTriangulated _ _

namespace HomComplex.CohomologyClass

variable (K L : CochainComplex C ℤ) (n : ℤ)
  [HasSmallLocalizedShiftedHom.{w} (HomologicalComplex.quasiIso C (.up ℤ)) ℤ K L]

set_option backward.isDefEq.respectTransparency false in

lemma bijective_toSmallShiftedHom_of_isKProjective [K.IsKProjective] :
    Function.Bijective (toSmallShiftedHom.{w} (K := K) (L := L) (n := n)) := by
  letI := HasDerivedCategory.standard C
  rw [← Function.Bijective.of_comp_iff'
      (SmallShiftedHom.equiv _ DerivedCategory.Q).bijective,
    ← Function.Bijective.of_comp_iff' (Iso.homCongr ((quotientCompQhIso C).symm.app K)
      ((Q.commShiftIso n).symm.app L ≪≫ (quotientCompQhIso C).symm.app (L⟦n⟧))).bijective]
  convert (CochainComplex.IsKProjective.Qh_map_bijective _ _).comp (toHom_bijective K L n)
  ext x
  obtain ⟨x, rfl⟩ := x.mk_surjective
  simp [toHom_mk, ShiftedHom.map]

variable {K L n} in
