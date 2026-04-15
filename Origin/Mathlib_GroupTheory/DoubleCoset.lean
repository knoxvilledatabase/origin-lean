/-
Extracted from GroupTheory/DoubleCoset.lean
Genuine: 6 of 7 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Double cosets

This file defines double cosets for two subgroups `H K` of a group `G` and the quotient of `G` by
the double coset relation, i.e. `H \ G / K`. We also prove that `G` can be written as a disjoint
union of the double cosets and that if one of `H` or `K` is the trivial group (i.e. `⊥` ) then
this is the usual left or right quotient of a group by a subgroup.

## Main definitions

* `setoid`: The double coset relation defined by two subgroups `H K` of `G`.
* `DoubleCoset.quotient`: The quotient of `G` by the double coset relation, i.e, `H \ G / K`.
-/

assert_not_exists MonoidWithZero

variable {G : Type*} [Group G] {α : Type*} [Mul α]

open MulOpposite

open scoped Pointwise

namespace DoubleCoset

def doubleCoset (a : α) (s t : Set α) : Set α :=
  s * {a} * t

lemma doubleCoset_eq_image2 (a : α) (s t : Set α) :
    doubleCoset a s t = Set.image2 (· * a * ·) s t := by
  simp_rw [doubleCoset, Set.mul_singleton, ← Set.image2_mul, Set.image2_image_left]

lemma mem_doubleCoset {s t : Set α} {a b : α} :
    b ∈ doubleCoset a s t ↔ ∃ x ∈ s, ∃ y ∈ t, b = x * a * y := by
  simp only [doubleCoset_eq_image2, Set.mem_image2, eq_comm]

lemma mem_doubleCoset_self (H K : Subgroup G) (a : G) : a ∈ doubleCoset a H K :=
  mem_doubleCoset.mpr ⟨1, H.one_mem, 1, K.one_mem, (one_mul a).symm.trans (mul_one (1 * a)).symm⟩

lemma doubleCoset_eq_of_mem {H K : Subgroup G} {a b : G} (hb : b ∈ doubleCoset a H K) :
    doubleCoset b H K = doubleCoset a H K := by
  obtain ⟨h, hh, k, hk, rfl⟩ := mem_doubleCoset.1 hb
  rw [doubleCoset, doubleCoset, ← Set.singleton_mul_singleton, ← Set.singleton_mul_singleton,
    mul_assoc, mul_assoc, Subgroup.singleton_mul_subgroup hk, ← mul_assoc, ← mul_assoc,
    Subgroup.subgroup_mul_singleton hh]

lemma eq_of_not_disjoint {H K : Subgroup G} {a b : G}
    (h : ¬Disjoint (doubleCoset a H K) (doubleCoset b H K)) :
    doubleCoset a H K = doubleCoset b H K := by
  rw [disjoint_comm] at h
  have ha : a ∈ doubleCoset b H K := mem_doubleCoset_of_not_disjoint h
  apply doubleCoset_eq_of_mem ha
