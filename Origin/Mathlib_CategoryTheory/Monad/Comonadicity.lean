/-
Extracted from CategoryTheory/Monad/Comonadicity.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Comonadicity theorems

We prove comonadicity theorems which can establish a given functor is comonadic. In particular, we
show three versions of Beck's comonadicity theorem, and the coreflexive (crude)
comonadicity theorem:

`F` is a comonadic left adjoint if it has a right adjoint, and:

* `C` has, `F` preserves and reflects `F`-split equalizers, see
  `CategoryTheory.Monad.comonadicOfHasPreservesReflectsFSplitEqualizers`
* `F` creates `F`-split coequalizers, see
  `CategoryTheory.Monad.comonadicOfCreatesFSplitEqualizers`
  (The converse of this is also shown, see
  `CategoryTheory.Monad.createsFSplitEqualizersOfComonadic`)
* `C` has and `F` preserves `F`-split equalizers, and `F` reflects isomorphisms, see
  `CategoryTheory.Monad.comonadicOfHasPreservesFSplitEqualizersOfReflectsIsomorphisms`
* `C` has and `F` preserves coreflexive equalizers, and `F` reflects isomorphisms, see
  `CategoryTheory.Monad.comonadicOfHasPreservesCoreflexiveEqualizersOfReflectsIsomorphisms`

This file has been adapted from `Mathlib/CategoryTheory/Monad/Monadicity.lean`.
Please try to keep them in sync.

## Tags

Beck, comonadicity, descent

-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Comonad

open Limits

noncomputable section

namespace ComonadicityInternal

variable {C : Type u₁} {D : Type u₂}

variable [Category.{v₁} C] [Category.{v₁} D]

variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): main_pair_coreflexive

-- INSTANCE (free from Core): main_pair_F_cosplit

def comparisonRightAdjointObj (A : adj.toComonad.Coalgebra)
    [HasEqualizer (G.map A.a) (adj.unit.app _)] : C :=
  equalizer (G.map A.a) (adj.unit.app _)

set_option backward.isDefEq.respectTransparency false in
