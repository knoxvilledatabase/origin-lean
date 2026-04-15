/-
Extracted from AlgebraicTopology/SingularHomology/HomotopyInvarianceTopCat.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Homotopy invariance of singular homology

In this file, we show that for any homotopy `H : TopCat.Homotopy f g`
between two morphisms `f : X ⟶ Y` and `g : X ⟶ Y` in `TopCat`,
the corresponding morphisms on the singular chain complexes
are homotopic, and in particular the induced morphisms
on singular homology are equal.

The proof proceeds by observing that this result is a particular
case of the homotopy invariance of the homology of simplicial sets
(see the file `Mathlib/AlgebraicTopology/SingularHomology/HomotopyInvariance.lean`),
applied to the morphisms `TopCat.toSSet.map f` and `TopCat.toSSet.map g`
between the singular simplicial sets of `X` and `Y`. That the homotopy `H`
induces a homotopy between these morphisms of simplicial sets
is the definition `TopCat.Homotopy.toSSet` which appeared in the file
`Mathlib/Topology/Homotopy/TopCat/ToSSet.lean`.

This result was first formalized in Lean 3 in 2022 by
Brendan Seamus Murphy (with a different proof).

-/

universe v u w

open AlgebraicTopology CategoryTheory Limits

namespace TopCat.Homotopy

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
  {X Y : TopCat.{w}} {f g : X ⟶ Y}

noncomputable def singularChainComplexFunctorObjMap (H : TopCat.Homotopy f g) (R : C) :
    _root_.Homotopy (((singularChainComplexFunctor C).obj R).map f)
      (((singularChainComplexFunctor C).obj R).map g) :=
  H.toSSet.chainComplexMap R

open HomologicalComplex in

lemma congr_homologyMap_singularChainComplexFunctor [CategoryWithHomology C]
    (H : TopCat.Homotopy f g) (R : C) (n : ℕ) :
    homologyMap (((singularChainComplexFunctor C).obj R).map f) n =
    homologyMap (((singularChainComplexFunctor C).obj R).map g) n :=
  (H.singularChainComplexFunctorObjMap R).homologyMap_eq n

end TopCat.Homotopy
