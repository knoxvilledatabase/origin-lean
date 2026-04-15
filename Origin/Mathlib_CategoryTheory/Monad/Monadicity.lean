/-
Extracted from CategoryTheory/Monad/Monadicity.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Monadicity theorems

We prove monadicity theorems which can establish a given functor is monadic. In particular, we
show three versions of Beck's monadicity theorem, and the reflexive (crude) monadicity theorem:

`G` is a monadic right adjoint if it has a left adjoint, and:

* `D` has, `G` preserves and reflects `G`-split coequalizers, see
  `CategoryTheory.Monad.monadicOfHasPreservesReflectsGSplitCoequalizers`
* `G` creates `G`-split coequalizers, see
  `CategoryTheory.Monad.monadicOfCreatesGSplitCoequalizers`
  (The converse of this is also shown, see
  `CategoryTheory.Monad.createsGSplitCoequalizersOfMonadic`)
* `D` has and `G` preserves `G`-split coequalizers, and `G` reflects isomorphisms, see
  `CategoryTheory.Monad.monadicOfHasPreservesGSplitCoequalizersOfReflectsIsomorphisms`
* `D` has and `G` preserves reflexive coequalizers, and `G` reflects isomorphisms, see
  `CategoryTheory.Monad.monadicOfHasPreservesReflexiveCoequalizersOfReflectsIsomorphisms`

This file has been adapted to `Mathlib/CategoryTheory/Monad/Comonadicity.lean`.
Please try to keep them in sync.

## Tags

Beck, monadicity, descent

-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Monad

open Limits

noncomputable section

namespace MonadicityInternal

variable {C : Type u₁} {D : Type u₂}

variable [Category.{v₁} C] [Category.{v₁} D]

variable {G : D ⥤ C} {F : C ⥤ D} (adj : F ⊣ G)

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): main_pair_reflexive

-- INSTANCE (free from Core): main_pair_G_split

def comparisonLeftAdjointObj (A : adj.toMonad.Algebra)
    [HasCoequalizer (F.map A.a) (adj.counit.app _)] : D :=
  coequalizer (F.map A.a) (adj.counit.app _)

set_option backward.isDefEq.respectTransparency false in
