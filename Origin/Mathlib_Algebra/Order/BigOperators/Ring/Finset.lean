/-
Extracted from Algebra/Order/BigOperators/Ring/Finset.lean
Genuine: 6 of 6 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Big operators on a finset in ordered rings

This file contains the results concerning the interaction of finset big operators with ordered
rings.

In particular, this file contains the standard form of the Cauchy-Schwarz inequality, as well as
some of its immediate consequences.
-/

variable {ι R S : Type*}

namespace Finset

section OrderedSemiring

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] {f : ι → R} {s : Finset ι}

lemma sum_sq_le_sq_sum_of_nonneg (hf : ∀ i ∈ s, 0 ≤ f i) :
    ∑ i ∈ s, f i ^ 2 ≤ (∑ i ∈ s, f i) ^ 2 := by
  simp only [sq, sum_mul_sum]
  refine sum_le_sum fun i hi ↦ ?_
  rw [← mul_sum]
  gcongr
  · exact hf i hi
  · exact single_le_sum hf hi

end OrderedSemiring

section OrderedCommSemiring

variable [CommSemiring R] [PartialOrder R] [IsOrderedRing R] {f g : ι → R} {s t : Finset ι}

lemma prod_add_prod_le {i : ι} {f g h : ι → R} (hi : i ∈ s) (h2i : g i + h i ≤ f i)
    (hgf : ∀ j ∈ s, j ≠ i → g j ≤ f j) (hhf : ∀ j ∈ s, j ≠ i → h j ≤ f j) (hg : ∀ i ∈ s, 0 ≤ g i)
    (hh : ∀ i ∈ s, 0 ≤ h i) : ((∏ i ∈ s, g i) + ∏ i ∈ s, h i) ≤ ∏ i ∈ s, f i := by
  classical
  simp_rw [prod_eq_mul_prod_diff_singleton_of_mem hi]
  refine le_trans ?_ (mul_le_mul_of_nonneg_right h2i ?_)
  · rw [right_distrib]
    gcongr with j hj <;> aesop
  · apply prod_nonneg
    simp only [and_imp, mem_sdiff, mem_singleton]
    exact fun j hj hji ↦ le_trans (hg j hj) (hgf j hj hji)

theorem le_prod_of_submultiplicative_on_pred_of_nonneg {M : Type*} [CommMonoid M] (f : M → R)
    (p : M → Prop) (h_nonneg : ∀ a, 0 ≤ f a) (h_one : f 1 ≤ 1)
    (h_mul : ∀ a b, p a → p b → f (a * b) ≤ f a * f b) (hp_mul : ∀ a b, p a → p b → p (a * b))
    (s : Finset ι) (g : ι → M) (hps : ∀ a, a ∈ s → p (g a)) :
    f (∏ i ∈ s, g i) ≤ ∏ i ∈ s, f (g i) := by
  apply le_trans (Multiset.le_prod_of_submultiplicative_on_pred_of_nonneg f p h_nonneg h_one
    h_mul hp_mul _ ?_) (by simp [Multiset.map_map])
  intro _ ha
  obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp ha
  exact hps i hi

theorem le_prod_of_submultiplicative_of_nonneg {M : Type*} [CommMonoid M]
    (f : M → R) (h_nonneg : ∀ a, 0 ≤ f a) (h_one : f 1 ≤ 1)
    (h_mul : ∀ x y : M, f (x * y) ≤ f x * f y) (s : Finset ι) (g : ι → M) :
    f (∏ i ∈ s, g i) ≤ ∏ i ∈ s, f (g i) :=
  le_trans (Multiset.le_prod_of_submultiplicative_of_nonneg f h_nonneg h_one h_mul _)
    (by simp [Multiset.map_map])

end OrderedCommSemiring

theorem sum_mul_self_eq_zero_iff [Semiring R] [LinearOrder R] [IsStrictOrderedRing R]
    [ExistsAddOfLE R] (s : Finset ι)
    (f : ι → R) : ∑ i ∈ s, f i * f i = 0 ↔ ∀ i ∈ s, f i = 0 := by
  rw [sum_eq_zero_iff_of_nonneg fun _ _ ↦ mul_self_nonneg _]
  simp

lemma abs_prod [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] (s : Finset ι) (f : ι → R) :
    |∏ x ∈ s, f x| = ∏ x ∈ s, |f x| :=
  map_prod absHom _ _
