/-
Extracted from LinearAlgebra/ConvexSpace/AffineSpace.lean
Genuine: 4 of 7 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Affine spaces are convex spaces

This file shows that every affine space is a convex space.

## Main results

* `AddTorsor.instConvexSpace`: An affine space over a module is a convex space.
* `AddTorsor.convexCombination_eq_affineCombination`: The convex combination equals the affine
  combination.
* `AddTorsor.convexComboPair_eq_lineMap`: Binary convex combinations are given by `lineMap`.
-/

noncomputable section

open scoped Affine

variable {R : Type*} {V : Type*} {P : Type*}

variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R]

variable [AddCommGroup V] [Module R V] [AddTorsor V P]

namespace AddTorsor

public def convexCombination (s : StdSimplex R P) : P :=
  s.weights.support.affineCombination R id s.weights

public theorem convexCombination_single (x : P) :
    convexCombination (StdSimplex.single x : StdSimplex R P) = x := by
  simp only [convexCombination, StdSimplex.single]
  rw [Finsupp.support_single_ne_zero _ one_ne_zero]
  exact ({x} : Finset P).affineCombination_of_eq_one_of_eq_zero _ _
    (Finset.mem_singleton_self x) Finsupp.single_eq_same fun j _ hne => Finsupp.single_eq_of_ne hne

-- INSTANCE (free from Core): instConvexSpace

public lemma _root_.convexCombination_eq_sum (f : StdSimplex R V) :
    letI : ConvexSpace R V := inferInstance
    ConvexSpace.convexCombination f = f.sum fun i r ↦ r • i := by
  simp [AddTorsor.convexCombination_eq_affineCombination,
    Finset.affineCombination_eq_linear_combination _ _ _ f.total, Finsupp.sum]

public theorem convexComboPair_eq_lineMap (s t : R) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (h : s + t = 1) (x y : P) :
    convexComboPair s t hs ht h x y = AffineMap.lineMap y x s := by
  simp only [convexComboPair, convexCombination_eq_affineCombination, StdSimplex.duple,
    AffineMap.lineMap_apply]
  classical
  -- Use weighted subtraction with base point y
  rw [Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ _ id (b := y)]
  swap
  · -- Prove sum of weights equals 1
    trans (Finsupp.single x s + Finsupp.single y t).sum fun _ r => r
    · apply Finset.sum_congr rfl
      intro i _
      simp only [Finsupp.coe_add, Pi.add_apply]
    · rw [Finsupp.sum_add_index (by simp) (by simp), Finsupp.sum_single_index (by simp),
        Finsupp.sum_single_index (by simp), h]
  -- Now simplify the weighted subtraction
  congr 1
  rw [Finset.weightedVSubOfPoint_apply]
  simp only [id]
  -- Convert to Finsupp.sum
  change (Finsupp.single x s + Finsupp.single y t).sum (fun p w => w • (p -ᵥ y)) = _
  rw [Finsupp.sum_add_index (by simp) (fun _ a b => by simp [add_smul]),
    Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
  simp [vsub_self]

end AddTorsor
