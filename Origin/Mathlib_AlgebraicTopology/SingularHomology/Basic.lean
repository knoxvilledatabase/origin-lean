/-
Extracted from AlgebraicTopology/SingularHomology/Basic.lean
Genuine: 7 of 11 | Dissolved: 2 | Infrastructure: 2
-/
import Origin.Core

/-!
# Singular homology

In this file, we define the singular chain complex and singular homology of a topological space.
We also calculate the homology of a totally disconnected space as an example.

-/

noncomputable section

namespace AlgebraicTopology

open CategoryTheory Limits

universe w v u

variable (C : Type u) [Category.{v} C] [HasCoproducts.{w} C]

variable [Preadditive C] (n : ℕ)

def singularChainComplexFunctor :
    C ⥤ TopCat.{w} ⥤ ChainComplex C ℕ :=
  SSet.chainComplexFunctor.{w} C ⋙ (Functor.whiskeringLeft _ _ _).obj TopCat.toSSet.{w}

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): [Limits.HasPullbacks

def singularHomologyFunctor [CategoryWithHomology C] : C ⥤ TopCat.{w} ⥤ C :=
  singularChainComplexFunctor C ⋙
    (Functor.whiskeringRight _ _ _).obj (HomologicalComplex.homologyFunctor _ _ n)

section Adjunction

open Limits _root_.SSet

open scoped Simplicial

open HomologicalComplex (eval)

def singularChainComplexFunctorAdjunction : (Functor.postcompose₂.obj (eval _ _ n)).obj
    (singularChainComplexFunctor C) ⊣ (evaluation _ _).obj (SimplexCategory.toTop.obj ⦋n⦌) :=
  ((SSet.chainComplexFunctorAdjunction C n).comp (sSetTopAdj.whiskerLeft _)).ofNatIsoRight
    ((evaluation TopCat C).mapIso (SSet.toTopSimplex.app _))

lemma singularChainComplexFunctorAdjunction_unit_app (R : C) :
    (singularChainComplexFunctorAdjunction C n).unit.app R =
      Sigma.ι (fun _ ↦ R) ((stdSimplexToTop.app ⦋n⦌).app (.op ⦋n⦌)
        (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌))) := by
  dsimp [singularChainComplexFunctorAdjunction, Adjunction.ofNatIsoRight,
    Adjunction.equivHomsetRightOfNatIso, Adjunction.homEquiv,
    Adjunction.comp, singularChainComplexFunctor,
    SSet.chainComplexFunctorAdjunction, SSet.chainComplexFunctor]
  simp [stdSimplexToTop]
  rfl

set_option backward.isDefEq.respectTransparency false in

lemma ι_singularChainComplexFunctorAdjunction_counit_app_app (F : TopCat ⥤ C) (X : TopCat) (i) :
    Sigma.ι _ i ≫ ((singularChainComplexFunctorAdjunction C n).counit.app F).app X =
      F.map i.down := by
  trans F.map (SSet.toTopSimplex.inv.app ⦋n⦌ ≫ SSet.toTop.map (SSet.yonedaEquiv.symm i) ≫
      sSetTopAdj.counit.app X)
  · dsimp [singularChainComplexFunctorAdjunction, Adjunction.ofNatIsoRight,
      Adjunction.equivHomsetRightOfNatIso, Adjunction.homEquiv,
      Adjunction.comp, singularChainComplexFunctor, SSet.chainComplexFunctor,
      SSet.chainComplexFunctorAdjunction]
    simp
  · congr 1
    rw [← reassoc_of% sSetTopAdj_unit_app_app_down]
    exact congr(($(sSetTopAdj.right_triangle_components X).app (.op ⦋n⦌) i).down)

end Adjunction

section TotallyDisconnectedSpace

variable (R : C) (X : TopCat.{w}) [TotallyDisconnectedSpace X]

noncomputable

def singularChainComplexFunctorIsoOfTotallyDisconnectedSpace :
    ((singularChainComplexFunctor C).obj R).obj X ≅
      (ChainComplex.alternatingConst.obj (∐ fun _ : X ↦ R)) :=
  (AlgebraicTopology.alternatingFaceMapComplex _).mapIso
    (((SimplicialObject.whiskering _ _).obj _).mapIso
    (TopCat.toSSetIsoConst X) ≪≫ Functor.constComp _ _ _) ≪≫
    AlgebraicTopology.alternatingFaceMapComplexConst.app _

-- DISSOLVED: singularChainComplexFunctor_exactAt_of_totallyDisconnectedSpace

-- DISSOLVED: isZero_singularHomologyFunctor_of_totallyDisconnectedSpace

noncomputable

def singularHomologyFunctorZeroOfTotallyDisconnectedSpace [CategoryWithHomology C] :
    ((singularHomologyFunctor C 0).obj R).obj X ≅ ∐ fun _ : X ↦ R :=
  have := hasCoproducts_shrink.{0, w} (C := C)
  have : HasZeroObject C := ⟨_, initialIsInitial.isZero⟩
  (HomologicalComplex.homologyFunctor _ _ 0).mapIso
      (singularChainComplexFunctorIsoOfTotallyDisconnectedSpace C R X) ≪≫
    ChainComplex.alternatingConstHomologyZero _

end TotallyDisconnectedSpace

end AlgebraicTopology
