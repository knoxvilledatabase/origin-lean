/-
Extracted from Topology/Bornology/BoundedOperation.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Bounded operations

This file introduces type classes for bornologically bounded operations.

In particular, when combined with type classes which guarantee continuity of the same operations,
we can equip bounded continuous functions with the corresponding operations.

## Main definitions

* `BoundedAdd R`: a class guaranteeing boundedness of addition.
* `BoundedSub R`: a class guaranteeing boundedness of subtraction.
* `BoundedMul R`: a class guaranteeing boundedness of multiplication.

-/

open scoped NNReal

section bounded_sub

/-!
### Bounded subtraction
-/

open Pointwise

class BoundedSub (R : Type*) [Bornology R] [Sub R] : Prop where
  isBounded_sub : ∀ {s t : Set R},
    Bornology.IsBounded s → Bornology.IsBounded t → Bornology.IsBounded (s - t)

variable {R : Type*}

lemma isBounded_sub [Bornology R] [Sub R] [BoundedSub R] {s t : Set R}
    (hs : Bornology.IsBounded s) (ht : Bornology.IsBounded t) :
    Bornology.IsBounded (s - t) := BoundedSub.isBounded_sub hs ht

lemma sub_bounded_of_bounded_of_bounded {X : Type*} [PseudoMetricSpace R] [Sub R] [BoundedSub R]
    {f g : X → R} (f_bdd : ∃ C, ∀ x y, dist (f x) (f y) ≤ C)
    (g_bdd : ∃ C, ∀ x y, dist (g x) (g y) ≤ C) :
    ∃ C, ∀ x y, dist ((f - g) x) ((f - g) y) ≤ C := by
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp <|
    isBounded_sub (Metric.isBounded_range_iff.mpr f_bdd) (Metric.isBounded_range_iff.mpr g_bdd)
  use C
  intro x y
  exact hC (Set.sub_mem_sub (Set.mem_range_self (f := f) x) (Set.mem_range_self (f := g) x))
           (Set.sub_mem_sub (Set.mem_range_self (f := f) y) (Set.mem_range_self (f := g) y))

lemma boundedSub_of_lipschitzWith_sub [PseudoMetricSpace R] [Sub R] {K : NNReal}
    (lip : LipschitzWith K (fun (p : R × R) ↦ p.1 - p.2)) :
    BoundedSub R where
  isBounded_sub {s t} s_bdd t_bdd := by
    have bdd : Bornology.IsBounded (s ×ˢ t) := Bornology.IsBounded.prod s_bdd t_bdd
    convert lip.isBounded_image bdd
    simp

end bounded_sub

section bounded_mul

/-!
### Bounded multiplication and addition
-/

open Pointwise Set

class BoundedAdd (R : Type*) [Bornology R] [Add R] : Prop where
  isBounded_add : ∀ {s t : Set R},
    Bornology.IsBounded s → Bornology.IsBounded t → Bornology.IsBounded (s + t)
