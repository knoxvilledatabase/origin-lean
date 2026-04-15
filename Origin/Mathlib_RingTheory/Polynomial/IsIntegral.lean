/-
Extracted from RingTheory/Polynomial/IsIntegral.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Results about coefficients of polynomials being integral

## Main results
- `Polynomial.isIntegral_coeff_of_dvd`: If a monic polynomial `p` divides another monic polynomial
  with integral coefficients, then the coefficients of `p` are themselves integral.
- `Polynomial.isIntegral_iff_isIntegral_coeff`:
  `p : S[X]` is integral over `R[X]` iff the coefficients of `p` are integral over `R`.
- `MvPolynomial.isIntegral_iff_isIntegral_coeff`: `p : MvPolynomial σ S` is integral over
  `MvPolynomial σ R` iff the coefficients of `p` are integral over `R`.
- We also provide the instance `[IsIntegrallyClosed R] : IsIntegrallyClosed R[X]`.

-/

variable {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]

namespace Polynomial

lemma isIntegral_coeff_prod
    (s : Finset ι) (p : ι → S[X]) (H : ∀ i ∈ s, ∀ j, IsIntegral R ((p i).coeff j)) (j : ℕ) :
    IsIntegral R ((s.prod p).coeff j) := by
  classical
  induction s using Finset.induction generalizing j with
  | empty => simp [coeff_one, apply_ite, isIntegral_zero, isIntegral_one]
  | insert a s has IH =>
    rw [Finset.prod_insert has, coeff_mul]
    exact IsIntegral.sum _ fun i hi ↦ .mul (H _ (by simp) _) (IH (fun _ _ ↦ H _ (by aesop)) _)

lemma isIntegral_coeff_of_factors (p : S[X])
    (hpmon : IsIntegral R p.leadingCoeff) (hp : p.Splits)
    (hpr : ∀ x, p.IsRoot x → IsIntegral R x) (i : ℕ) :
    IsIntegral R (p.coeff i) := by
  classical
  obtain ⟨m, hm⟩ := Polynomial.splits_iff_exists_multiset.mp hp
  rw [hm, Multiset.prod_eq_prod_coe, coeff_C_mul]
  refine .mul hpmon (isIntegral_coeff_prod _ _ ?_ _)
  have H {x} (hx : x ∈ m) : p.IsRoot x := by
    rw [IsRoot, hm, eval_mul, eval_multiset_prod, Multiset.prod_eq_zero, mul_zero]
    simpa [sub_eq_zero]
  rintro ⟨a, ⟨i, hi⟩⟩ -
  obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp (Multiset.count_pos.mp (i.zero_le.trans_lt hi))
  simp [coeff_X, coeff_C, IsIntegral.sub, apply_ite (IsIntegral R),
    isIntegral_one, isIntegral_zero, hpr x (H hx)]

open scoped TensorProduct in
