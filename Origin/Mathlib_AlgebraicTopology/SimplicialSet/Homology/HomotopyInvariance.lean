/-
Extracted from AlgebraicTopology/SimplicialSet/Homology/HomotopyInvariance.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Homotopy invariance of simplicial homology

This file proves that homotopic morphisms of simplicial sets induce
the same maps on singular homology (with coefficients in an object `R`
of a preadditive category `C` with coproducts).

First, in the case where the homotopy between two morphisms of simplicial sets
`f : X ⟶ Y` and `g : X ⟶ Y` is given as combinatorial simplicial homotopy
(`SimplicialObject.Homotopy`), i.e. as family of morphisms `X _⦋n⦌ ⟶ Y _⦋n + 1⦌`,
we use the fact that we still have a similar kind of homotopy between
the corresponding morphisms on the simplicial objects in `C` that are
obtained after applying the "free object" functor `sigmaConst.obj R : Type _ ⥤ C`
degreewise, and that a combinatoral homotopy of simplicial objects
in a preadditive category induces a homotopy on the alternating face map
complexes (see `SimplicialObject.Homotopy.toChainHomotopy`, which is defined
in the file `Mathlib/AlgebraicTopology/SimplicialObject/ChainHomotopy.lean`).

Secondly, in the case where the homotopy between `f` and `g` is given
by a usual homotopy of morphisms of simplicial sets (`SSet.Homotopy`),
i.e. by a morphism `h : X ⊗ Δ[1] ⟶ Y`, we apply the construction above
to the combinatorial simplicial homotopy that is deduced from `h` by
using the definition `SSet.Homotopy.toSimplicialObjectHomotopy` from the file
`Mathlib/AlgebraicTopology/SimplicialSet/Homotopy.lean`.

-/

/-! The invariance of singular homology (of topological spaces)
is obtained in the file
`Mathlib/AlgebraicTopology/SingularHomology/HomotopyInvarianceTopCat.lean`. -/

assert_not_exists TopologicalSpace

universe v u w

open CategoryTheory Limits AlgebraicTopology.SSet

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
  {X Y : SSet.{w}} {f g : X ⟶ Y}

namespace CategoryTheory.SimplicialObject.Homotopy

noncomputable def sSetChainComplexMap
    (H : SimplicialObject.Homotopy f g) (R : C) :
    _root_.Homotopy (SSet.chainComplexMap f R) (SSet.chainComplexMap g R) :=
  toChainHomotopy (H.whiskerRight _)
