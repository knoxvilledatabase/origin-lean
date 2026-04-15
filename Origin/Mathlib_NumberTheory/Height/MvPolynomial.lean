/-
Extracted from NumberTheory/Height/MvPolynomial.lean
Genuine: 10 of 11 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Height bounds for linear and polynomial maps

We prove an upper bound for the height of the image of a tuple under a linear map.

We also prove upper and lower bounds for the height of `fun i ↦ eval P i x`, where `P` is a family
of homogeneous polynomials over the field `K` of the same degree `N` and `x : ι → K`
with `ι` finite.
-/

section aux

private lemma Height.iSup_fun_eq_max (f : Fin 2 → ℝ) : iSup f = max (f 0) (f 1) := by
  rw [show f = ![f 0, f 1] from List.ofFn_inj.mp rfl]
  exact (max_eq_iSup ..).symm

namespace IsNonarchimedean

variable {R α : Type*} [CommRing R]

lemma apply_sum_le {α β F : Type*} [AddCommMonoid β] [FunLike F β ℝ] [NonnegHomClass F β ℝ]
    [ZeroHomClass F β ℝ] {v : F} (hv : IsNonarchimedean v) {l : α → β} {s : Finset α} :
    v (∑ i ∈ s, l i) ≤ ⨆ i : s, v (l i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    grw [hv .., ih]
    refine max_le ?_ ?_
    · exact Finite.le_ciSup_of_le ⟨_, s.mem_insert_self a⟩ le_rfl
    · rcases isEmpty_or_nonempty s with hs | hs
      · simpa using Real.iSup_nonneg_of_nonnegHomClass v _
      exact ciSup_le fun i ↦ Finite.le_ciSup_of_le (⟨i.val, Finset.mem_insert_of_mem i.prop⟩) le_rfl

end IsNonarchimedean

end aux

/-!
### Upper bound for the height of the image under a linear map
-/

variable {K : Type*} [Field K] {ι ι' : Type*} [Fintype ι] [Finite ι']

lemma AbsoluteValue.iSup_abv_linearMap_apply_le (v : AbsoluteValue K ℝ) (A : ι' × ι → K)
    (x : ι → K) :
    ⨆ j, v (∑ i, A (j, i) * x i) ≤ Nat.card ι * (⨆ ji, v (A ji)) * ⨆ i, v (x i) := by
  rcases isEmpty_or_nonempty ι'
  · simp
  refine ciSup_le fun j ↦ ?_
  grw [v.sum_le]
  simp only [map_mul]
  grw [Finset.sum_le_sum (g := fun _ ↦ (⨆ ji, v (A ji)) * ⨆ i, v (x i)) fun i _ ↦ ?h]
  case h =>
    dsimp only
    gcongr
    · exact Real.iSup_nonneg_of_nonnegHomClass v _
    · exact Finite.le_ciSup_of_le (j, i) le_rfl
    · exact Finite.le_ciSup_of_le i le_rfl
  rw [Finset.sum_const, nsmul_eq_mul, mul_assoc, Finset.card_univ, Nat.card_eq_fintype_card]

lemma IsNonarchimedean.iSup_abv_linearMap_apply_le {v : AbsoluteValue K ℝ} (hv : IsNonarchimedean v)
    (A : ι' × ι → K) (x : ι → K) :
    ⨆ j, v (∑ i, A (j, i) * x i) ≤ (⨆ ji, v (A ji)) * ⨆ i, v (x i) := by
  rcases isEmpty_or_nonempty ι
  · simp
  rcases isEmpty_or_nonempty ι'
  · simp
  refine ciSup_le fun j ↦ ?_
  grw [hv.apply_sum_le]
  simp only [map_mul]
  have (f : ι → ℝ) : ⨆ i : ↥Finset.univ, f i.val = ⨆ i, f i :=
    Function.Surjective.iSup_comp (fun i ↦ ⟨⟨i, Finset.mem_univ i⟩, rfl⟩) f
  rw [this fun i ↦ v (A (j, i)) * v (x i)]
  refine ciSup_le fun i ↦ ?_
  gcongr
  · exact Real.iSup_nonneg_of_nonnegHomClass v _
  · exact Finite.le_ciSup_of_le (j, i) le_rfl
  · exact Finite.le_ciSup_of_le i le_rfl

namespace Height

variable [AdmissibleAbsValues K]

open AdmissibleAbsValues

open Multiset in

theorem mulHeight_linearMap_apply_le [Nonempty ι] (A : ι' × ι → K) (x : ι → K) :
    mulHeight (fun j ↦ ∑ i, A (j, i) * x i) ≤
      Nat.card ι ^ totalWeight K * mulHeight A * mulHeight x := by
  have H₀ : 1 ≤ Nat.card ι ^ totalWeight K * mulHeight A * mulHeight x := by
    rw [show (1 : ℝ) = 1 * 1 * 1 by ring]
    gcongr
    · exact_mod_cast Nat.one_le_pow _ _ Nat.card_pos
    · exact one_le_mulHeight _
    · exact one_le_mulHeight _
  rcases isEmpty_or_nonempty ι' with hι' | hι'
  · simpa only [mulHeight_eq_one_of_subsingleton, mul_one] using H₀
  rcases eq_or_ne (fun j ↦ ∑ i, A (j, i) * x i) 0 with h | h
  · simpa only [h, mulHeight_zero] using H₀
  rcases eq_or_ne A 0 with rfl | hA
  · simpa using H₀
  rcases eq_or_ne x 0 with rfl | hx
  · simpa using H₀
  rw [mulHeight_eq h, mulHeight_eq hA, mulHeight_eq hx, mul_mul_mul_comm, ← mul_assoc, ← mul_assoc,
    mul_assoc (_ * _ * _)]
  gcongr
  · exact finprod_nonneg fun v ↦ Real.iSup_nonneg_of_nonnegHomClass v.val _
  · refine mul_nonneg (mul_nonneg (by simp) ?_) ?_ <;>
      exact prod_map_nonneg fun v _ ↦ Real.iSup_nonneg_of_nonnegHomClass v _
  · -- archimedean part: reduce to "local" statement `linearMap_apply_bound`
    rw [mul_assoc, ← prod_map_mul, ← prod_replicate, totalWeight, ← map_const', ← prod_map_mul]
    refine prod_map_le_prod_map₀ _ _ (fun v _ ↦ Real.iSup_nonneg_of_nonnegHomClass v _) fun v _ ↦ ?_
    rw [mul_comm (iSup _), ← mul_assoc]
    exact v.iSup_abv_linearMap_apply_le A x
  · -- nonarchimedean part: reduce to "local" statement `linearMap_apply_bound_of_isNonarchimedean`
    rw [← finprod_mul_distrib (by fun_prop (disch := assumption))
      (by fun_prop (disch := assumption))]
    refine finprod_le_finprod (by fun_prop (disch := assumption))
      (fun v ↦ Real.iSup_nonneg_of_nonnegHomClass v.val _) ?_ fun v ↦ ?_
    · fun_prop (disch := assumption)
    · exact (isNonarchimedean _ v.prop).iSup_abv_linearMap_apply_le A x

open Real in

theorem logHeight_linearMap_apply_le (A : ι' × ι → K) (x : ι → K) :
    logHeight (fun j ↦ ∑ i, A (j, i) * x i) ≤
      totalWeight K * log (Nat.card ι) + logHeight A + logHeight x := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · suffices 0 ≤ logHeight A + logHeight x by simp
    positivity
  simp only [logHeight_eq_log_mulHeight]
  have : (Nat.card ι : ℝ) ^ totalWeight K ≠ 0 := by simp
  pull (disch := first | assumption | positivity) log
  exact (log_le_log <| by positivity) <| mulHeight_linearMap_apply_le ..

end Height

/-!
### Upper bound for the height of the image under a polynomial map

If `p : ι' → MvPolynomial ι K` is a family of homogeneous polynomials of the same degree `N`
and `x : ι → K`, then the multiplicative height of `fun j ↦ (p j).eval x` is bounded above by
an (explicit) constant depending only on `p` times the `N`th power of the multiplicative
height of `x`. A similar statement holds for the logarithmic height.
-/

open MvPolynomial

variable {K : Type*} [Field K] {ι : Type*}

lemma AbsoluteValue.eval_mvPolynomial_le [Finite ι] (v : AbsoluteValue K ℝ)
    {p : MvPolynomial ι K} {N : ℕ} (hp : p.IsHomogeneous N) (x : ι → K) :
    v (p.eval x) ≤ p.sum (fun _ c ↦ v c) * (⨆ i, v (x i)) ^ N := by
  rw [eval_eq, sum_def, Finset.sum_mul]
  grw [AbsoluteValue.sum_le]
  simp_rw [v.map_mul, v.map_prod, v.map_pow]
  refine Finset.sum_le_sum fun s hs ↦ ?_
  gcongr
  rw [hp.degree_eq_sum_deg_support hs, ← Finset.prod_pow_eq_pow_sum]
  gcongr with i
  exact Finite.le_ciSup (fun j ↦ v (x j)) i

lemma IsNonarchimedean.eval_mvPolynomial_le [Finite ι] {v : AbsoluteValue K ℝ}
    (hv : IsNonarchimedean v) {p : MvPolynomial ι K} {N : ℕ} (hp : p.IsHomogeneous N) (x : ι → K) :
    v (p.eval x) ≤ (⨆ s : p.support, v (coeff s p)) * (⨆ i, v (x i)) ^ N := by
  rcases eq_or_ne p 0 with rfl | hp₀
  · simp_all
  rw [eval_eq]
  obtain ⟨s, hs₁, hs₂⟩ :=
    hv.finset_image_add_of_nonempty (fun d ↦ coeff d p * ∏ i ∈ d.support, x i ^ d i)
      (support_nonempty.mpr hp₀)
  grw [hs₂]
  simp_rw [v.map_mul, v.map_prod, v.map_pow]
  gcongr
  · exact Real.iSup_nonneg_of_nonnegHomClass v _
  · exact Finite.le_ciSup_of_le (⟨s, hs₁⟩ : p.support) le_rfl
  · rw [hp.degree_eq_sum_deg_support hs₁, ← Finset.prod_pow_eq_pow_sum]
    gcongr with i
    exact Finite.le_ciSup (fun j ↦ v (x j)) i

namespace Height

variable {ι' : Type*}

variable [AdmissibleAbsValues K]

open AdmissibleAbsValues

def mulHeightBound (p : ι' → MvPolynomial ι K) : ℝ :=
  (archAbsVal.map fun v ↦ ⨆ j, (p j).sum (fun _ c ↦ v c)).prod *
    ∏ᶠ v : nonarchAbsVal, ⨆ j, max (⨆ s : (p j).support, v.val (coeff s (p j))) 1

variable (K ι ι') in

lemma max_mulHeightBound_zero_one_eq_one :
    max (mulHeightBound (0 : ι' → MvPolynomial ι K)) 1 = 1 := by
  simp only [mulHeightBound_eq, Pi.zero_apply, support_zero, coeff_zero, AbsoluteValue.map_zero,
    Real.iSup_of_isEmpty, zero_le_one, sup_of_le_right]
  set_option backward.isDefEq.respectTransparency false in -- temporary measure
  simp only [Finsupp.sum_zero_index] -- singling this out for needing the above
  simp only [Real.iSup_const_zero, Multiset.map_const', Multiset.prod_replicate, zero_pow_eq]
  rcases isEmpty_or_nonempty ι'
  · split_ifs
    · simpa using finprod_zero_le_one
    · simp
  · simp
    grind

variable [Finite ι']

open Function in
