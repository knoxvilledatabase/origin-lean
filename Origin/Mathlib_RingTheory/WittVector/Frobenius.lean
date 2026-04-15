/-
Extracted from RingTheory/WittVector/Frobenius.lean
Genuine: 8 of 9 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
## The Frobenius operator

If `R` has characteristic `p`, then there is a ring endomorphism `frobenius R p`
that raises `r : R` to the power `p`.
By applying `WittVector.map` to `frobenius R p`, we obtain a ring endomorphism `𝕎 R →+* 𝕎 R`.
It turns out that this endomorphism can be described by polynomials over `ℤ`
that do not depend on `R` or the fact that it has characteristic `p`.
In this way, we obtain a Frobenius endomorphism `WittVector.frobeniusFun : 𝕎 R → 𝕎 R`
for every commutative ring `R`.

Unfortunately, the aforementioned polynomials cannot be obtained using the machinery
of `wittStructureInt` that was developed in `StructurePolynomial.lean`.
We therefore have to define the polynomials by hand, and check that they have the required property.

In case `R` has characteristic `p`, we show in `frobenius_eq_map_frobenius`
that `WittVector.frobeniusFun` is equal to `WittVector.map (frobenius R p)`.

### Main definitions and results

* `frobeniusPoly`: the polynomials that describe the coefficients of `frobeniusFun`;
* `frobeniusFun`: the Frobenius endomorphism on Witt vectors;
* `frobeniusFun_isPoly`: the tautological assertion that Frobenius is a polynomial function;
* `frobenius_eq_map_frobenius`: the fact that in characteristic `p`, Frobenius is equal to
  `WittVector.map (frobenius R p)`.

TODO: Show that `WittVector.frobeniusFun` is a ring homomorphism,
and bundle it into `WittVector.frobenius`.

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]
-/

namespace WittVector

variable {p : ℕ} {R : Type*} [hp : Fact p.Prime] [CommRing R]

local notation "𝕎" => WittVector p -- type as `\bbW`

noncomputable section

open MvPolynomial Finset

variable (p)

def frobeniusPolyRat (n : ℕ) : MvPolynomial ℕ ℚ :=
  bind₁ (wittPolynomial p ℚ ∘ fun n => n + 1) (xInTermsOfW p ℚ n)

theorem bind₁_frobeniusPolyRat_wittPolynomial (n : ℕ) :
    bind₁ (frobeniusPolyRat p) (wittPolynomial p ℚ n) = wittPolynomial p ℚ (n + 1) := by
  delta frobeniusPolyRat
  rw [← bind₁_bind₁, bind₁_xInTermsOfW_wittPolynomial, bind₁_X_right, Function.comp_apply]

local notation "v" => multiplicity

noncomputable def frobeniusPolyAux : ℕ → MvPolynomial ℕ ℤ
  | n => X (n + 1) - ∑ i : Fin n, have _ := i.is_lt
      ∑ j ∈ range (p ^ (n - i)),
        (((X (i : ℕ) ^ p) ^ (p ^ (n - (i : ℕ)) - (j + 1)) : MvPolynomial ℕ ℤ) *
        (frobeniusPolyAux i) ^ (j + 1)) *
        C (((p ^ (n - i)).choose (j + 1) / (p ^ (n - i - v p (j + 1)))
          * ↑p ^ (j - v p (j + 1)) : ℕ) : ℤ)

omit hp in

theorem frobeniusPolyAux_eq (n : ℕ) :
    frobeniusPolyAux p n =
      X (n + 1) - ∑ i ∈ range n,
          ∑ j ∈ range (p ^ (n - i)),
            (X i ^ p) ^ (p ^ (n - i) - (j + 1)) * frobeniusPolyAux p i ^ (j + 1) *
              C ↑((p ^ (n - i)).choose (j + 1) / p ^ (n - i - v p (j + 1)) *
                ↑p ^ (j - v p (j + 1)) : ℕ) := by
  rw [frobeniusPolyAux, ← Fin.sum_univ_eq_sum_range]

def frobeniusPoly (n : ℕ) : MvPolynomial ℕ ℤ :=
  X n ^ p + C (p : ℤ) * frobeniusPolyAux p n

theorem map_frobeniusPoly.key₁ (n j : ℕ) (hj : j < p ^ n) :
    p ^ (n - v p (j + 1)) ∣ (p ^ n).choose (j + 1) := by
  apply pow_dvd_of_le_emultiplicity
  rw [hp.out.emultiplicity_choose_prime_pow hj j.succ_ne_zero]

theorem map_frobeniusPoly (n : ℕ) :
    MvPolynomial.map (Int.castRingHom ℚ) (frobeniusPoly p n) = frobeniusPolyRat p n := by
  rw [frobeniusPoly, map_add, map_mul, map_pow, map_C, map_X, eq_intCast, Int.cast_natCast,
    frobeniusPolyRat]
  refine Nat.strong_induction_on n ?_; clear n
  intro n IH
  rw [xInTermsOfW_eq]
  simp only [map_sum, map_sub, map_mul, map_pow (bind₁ _), bind₁_C_right]
  have h1 : (p : ℚ) ^ n * ⅟(p : ℚ) ^ n = 1 := by rw [← mul_pow, mul_invOf_self, one_pow]
  rw [bind₁_X_right, Function.comp_apply, wittPolynomial_eq_sum_C_mul_X_pow, sum_range_succ,
    sum_range_succ, tsub_self, add_tsub_cancel_left, pow_zero, pow_one, pow_one, sub_mul, add_mul,
    add_mul, mul_right_comm, mul_right_comm (C ((p : ℚ) ^ (n + 1))), ← C_mul, ← C_mul, pow_succ',
    mul_assoc (p : ℚ) ((p : ℚ) ^ n), h1, mul_one, C_1, one_mul, add_comm _ (X n ^ p), add_assoc,
    ← add_sub, add_right_inj, frobeniusPolyAux_eq, map_sub, map_X, mul_sub, sub_eq_add_neg,
    add_comm _ (C (p : ℚ) * X (n + 1)), ← add_sub,
    add_right_inj, neg_eq_iff_eq_neg, neg_sub, eq_comm]
  simp only [map_sum, mul_sum, sum_mul, ← sum_sub_distrib]
  apply sum_congr rfl
  intro i hi
  rw [mem_range] at hi
  rw [← IH i hi]
  clear IH
  rw [add_comm (X i ^ p), add_pow, sum_range_succ', pow_zero, tsub_zero, Nat.choose_zero_right,
    one_mul, Nat.cast_one, mul_one, mul_add, add_mul, Nat.succ_sub (le_of_lt hi),
    Nat.succ_eq_add_one (n - i), pow_succ', pow_mul, add_sub_cancel_right, mul_sum, sum_mul]
  apply sum_congr rfl
  intro j hj
  rw [mem_range] at hj
  rw [map_mul, map_mul, map_pow, map_pow, map_pow, map_pow, map_pow, map_C, map_X, mul_pow]
  rw [mul_comm (C (p : ℚ) ^ i), mul_comm _ ((X i ^ p) ^ _), mul_comm (C (p : ℚ) ^ (j + 1)),
    mul_comm (C (p : ℚ))]
  simp only [mul_assoc]
  apply congr_arg
  apply congr_arg
  rw [← C_eq_coe_nat]
  simp only [← map_pow, ← C_mul]
  rw [C_inj]
  simp only [invOf_eq_inv, eq_intCast, inv_pow, Int.cast_natCast, Nat.cast_mul, Int.cast_mul]
  rw [Rat.natCast_div _ _ (map_frobeniusPoly.key₁ p (n - i) j hj)]
  push_cast
  linear_combination (norm := skip) -p / p ^ n / p ^ (n - i - v p (j + 1))
    * (p ^ (n - i)).choose (j + 1) * congr((p : ℚ) ^ $(map_frobeniusPoly.key₂ p hi.le hj))
  field [hp.1.ne_zero]

theorem frobeniusPoly_zmod (n : ℕ) :
    MvPolynomial.map (Int.castRingHom (ZMod p)) (frobeniusPoly p n) = X n ^ p := by
  rw [frobeniusPoly, map_add, map_pow, map_mul, map_X, map_C]
  simp only [Int.cast_natCast, add_zero, eq_intCast, ZMod.natCast_self, zero_mul, C_0]
