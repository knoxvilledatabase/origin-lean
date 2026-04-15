/-
Extracted from Analysis/Normed/Unbundled/SeminormFromConst.lean
Genuine: 8 of 9 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# SeminormFromConst


In this file, we prove [BGR, Proposition 1.3.2/2][bosch-guntzer-remmert] : starting from a
power-multiplicative seminorm on a commutative ring `R` and a nonzero `c : R`, we create a new
power-multiplicative seminorm for which `c` is multiplicative.

## Main Definitions

* `seminormFromConst'` : the real-valued function sending `x ∈ R` to the limit of
  `(f (x * c^n))/((f c)^n)`.
* `seminormFromConst` : the function `seminormFromConst'` as a `RingSeminorm` on `R`.


## Main Results
* `seminormFromConst_isNonarchimedean` : the function `seminormFromConst' c f`
  is nonarchimedean when f is nonarchimedean.
* `seminormFromConst_isPowMul` : the function `seminormFromConst' c f`
  is power-multiplicative.
* `seminormFromConst_const_mul` : for every `x : R`, `seminormFromConst' c f (c * x)`
  equals the product `seminormFromConst' c f c * seminormFromConst' c f x`.

## References
* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert]

## Tags

SeminormFromConst, Seminorm, Nonarchimedean
-/

noncomputable section

open Filter

open scoped Topology

section Ring

variable {R : Type*} [CommRing R] (c : R) (f : RingSeminorm R)

def seminormFromConst_seq (x : R) : ℕ → ℝ := fun n ↦ f (x * c ^ n) / f c ^ n

theorem seminormFromConst_seq_nonneg (x : R) : 0 ≤ seminormFromConst_seq c f x :=
  fun n ↦ div_nonneg (apply_nonneg f (x * c ^ n)) (pow_nonneg (apply_nonneg f c) n)

theorem seminormFromConst_bddBelow (x : R) :
    BddBelow (Set.range (seminormFromConst_seq c f x)) := by
  use 0
  rintro r ⟨n, rfl⟩
  exact seminormFromConst_seq_nonneg c f x n

variable {f}

theorem seminormFromConst_seq_zero (hf : f 0 = 0) : seminormFromConst_seq c f 0 = 0 := by
  rw [seminormFromConst_seq_def]
  ext n
  rw [zero_mul, hf, zero_div, Pi.zero_apply]

variable {c}

variable (hf1 : f 1 ≤ 1) (hc : f c ≠ 0) (hpm : IsPowMul f)

include hpm hc

theorem seminormFromConst_seq_one (n : ℕ) (hn : 1 ≤ n) : seminormFromConst_seq c f 1 n = 1 := by
  simp only [seminormFromConst_seq]
  rw [one_mul, hpm _ hn, div_self (pow_ne_zero n hc)]

include hf1

theorem seminormFromConst_seq_antitone (x : R) : Antitone (seminormFromConst_seq c f x) := by
  intro m n hmn
  simp only [seminormFromConst_seq]
  nth_rw 1 [← Nat.add_sub_of_le hmn]
  rw [pow_add, ← mul_assoc]
  have hc_pos : 0 < f c := lt_of_le_of_ne (apply_nonneg f _) hc.symm
  apply le_trans ((div_le_div_iff_of_pos_right (pow_pos hc_pos _)).mpr (map_mul_le_mul f _ _))
  cases hmn.eq_or_lt with
  | inl heq =>
    have hnm : n - m = 0 := by rw [heq, Nat.sub_self n]
    rw [hnm, heq, div_le_div_iff_of_pos_right (pow_pos hc_pos _), pow_zero]
    conv_rhs => rw [← mul_one (f (x * c ^ n))]
    gcongr
  | inr hlt =>
    have h1 : 1 ≤ n - m := by
      rw [Nat.one_le_iff_ne_zero]
      exact Nat.sub_ne_zero_of_lt hlt
    rw [hpm c h1, mul_div_assoc, div_eq_mul_inv, pow_sub₀ _ hc hmn, mul_assoc, mul_comm (f c ^ m)⁻¹,
      ← mul_assoc (f c ^ n), mul_inv_cancel₀ (pow_ne_zero n hc), one_mul, div_eq_mul_inv]

def seminormFromConst' (c : R) (f : RingSeminorm R) (x : R) : ℝ :=
  iInf (seminormFromConst_seq c f x)

theorem tendsto_seminormFromConst_seq_atTop (x : R) :
    Tendsto (seminormFromConst_seq c f x) atTop (𝓝 (seminormFromConst' c f x)) :=
  tendsto_atTop_ciInf (seminormFromConst_seq_antitone hf1 hc hpm x)
    (seminormFromConst_bddBelow c f x)
