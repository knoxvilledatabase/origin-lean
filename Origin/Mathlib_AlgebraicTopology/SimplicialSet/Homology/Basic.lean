/-
Extracted from AlgebraicTopology/SimplicialSet/Homology/Basic.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Simplicial homology

In this file, we define the homology of simplicial sets.
For any preadditive category `C` with coproducts of size `w` and any
object `R : C`, the simplicial chain complex of a simplicial
set `X` is denoted `X.chainComplex R`, and its homology
in degree `n : ℕ` is `X.homology R n`.

-/

open Simplicial CategoryTheory Limits

universe w v u

namespace SSet

variable (C : Type u) [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]

noncomputable def chainComplexFunctor : C ⥤ SSet.{w} ⥤ ChainComplex C ℕ :=
  (Functor.postcompose₂.obj (AlgebraicTopology.alternatingFaceMapComplex _)).obj
    (sigmaConst ⋙ SimplicialObject.whiskering _ _)

-- INSTANCE (free from Core): :
