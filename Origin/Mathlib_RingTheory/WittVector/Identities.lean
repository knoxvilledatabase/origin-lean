/-
Extracted from RingTheory/WittVector/Identities.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
## Identities between operations on the ring of Witt vectors

In this file we derive common identities between the Frobenius and Verschiebung operators.

## Main declarations

* `frobenius_verschiebung`: the composition of Frobenius and Verschiebung is multiplication by `p`
* `verschiebung_mul_frobenius`: the “projection formula”: `V(x * F y) = V x * y`
* `iterate_verschiebung_mul_coeff`: an identity from [Haze09] 6.2

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]
-/

namespace WittVector

variable {p : ℕ} {R : Type*} [hp : Fact p.Prime] [CommRing R]

local notation "𝕎" => WittVector p

noncomputable section

theorem frobenius_verschiebung (x : 𝕎 R) : frobenius (verschiebung x) = x * p := by
  have : IsPoly p fun {R} [CommRing R] x ↦ frobenius (verschiebung x) :=
    IsPoly.comp (hg := frobenius_isPoly p) (hf := verschiebung_isPoly)
  have : IsPoly p fun {R} [CommRing R] x ↦ x * p := mulN_isPoly p p
  ghost_calc x
  ghost_simp [mul_comm]

theorem verschiebung_zmod (x : 𝕎 (ZMod p)) : verschiebung x = x * p := by
  rw [← frobenius_verschiebung, frobenius_zmodp]

variable (p R)

theorem coeff_p_pow [CharP R p] (i : ℕ) : ((p : 𝕎 R) ^ i).coeff i = 1 := by
  induction i with
  | zero => simp only [one_coeff_zero, pow_zero]
  | succ i h =>
    rw [pow_succ, ← frobenius_verschiebung, coeff_frobenius_charP,
      verschiebung_coeff_succ, h, one_pow]

theorem coeff_p_pow_eq_zero [CharP R p] {i j : ℕ} (hj : j ≠ i) : ((p : 𝕎 R) ^ i).coeff j = 0 := by
  induction i generalizing j with
  | zero =>
    rw [pow_zero, one_coeff_eq_of_pos]
    exact Nat.pos_of_ne_zero hj
  | succ i hi =>
    rw [pow_succ, ← frobenius_verschiebung, coeff_frobenius_charP]
    cases j
    · rw [verschiebung_coeff_zero, zero_pow hp.out.ne_zero]
    · rw [verschiebung_coeff_succ, hi (ne_of_apply_ne _ hj), zero_pow hp.out.ne_zero]

theorem coeff_p [CharP R p] (i : ℕ) : (p : 𝕎 R).coeff i = if i = 1 then 1 else 0 := by
  split_ifs with hi
  · simpa only [hi, pow_one] using coeff_p_pow p R 1
  · simpa only [pow_one] using coeff_p_pow_eq_zero p R hi
