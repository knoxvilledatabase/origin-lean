/-
Extracted from GroupTheory/FinitelyPresentedGroup.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Finitely Presented Groups

This file defines finitely presented groups.

## Main definitions
* `Subgroup.IsNormalClosureFG N`: says that the subgroup `N` is the normal closure of a
  finitely generated subgroup.
* `IsFinitelyPresented`: defines when a group is finitely presented.

## Main results
* `Subgroup.IsNormalClosureFG_map`: Being the normal closure of a finite set is preserved under
  surjective homomorphism.
* `IsFinitelyPresented.equiv`: finitely presented groups are closed under isomorphism.

## Tags
finitely presented group, finitely generated normal closure
-/

variable {G H α β : Type*} [Group G] [Group H]

def Subgroup.IsNormalClosureFG (N : Subgroup G) : Prop :=
  ∃ S : Set G, S.Finite ∧ Subgroup.normalClosure S = N

namespace Subgroup.IsNormalClosureFG

protected theorem map {N : Subgroup G} (hN : IsNormalClosureFG N)
    {f : G →* H} (hf : Function.Surjective f) : (N.map f).IsNormalClosureFG := by
  obtain ⟨S, hSfinite, hSclosure⟩ := hN
  refine ⟨f '' S, hSfinite.image _, ?_⟩
  rw [← hSclosure, Subgroup.map_normalClosure _ _ hf]

end Subgroup.IsNormalClosureFG
