/-
Extracted from RingTheory/WittVector/DiscreteValuationRing.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Witt vectors over a perfect ring

This file establishes that Witt vectors over a perfect field are a discrete valuation ring.
When `k` is a perfect ring, a nonzero `a : 𝕎 k` can be written as `p^m * b` for some `m : ℕ` and
`b : 𝕎 k` with nonzero 0th coefficient.
When `k` is also a field, this `b` can be chosen to be a unit of `𝕎 k`.

## Main declarations

* `WittVector.exists_eq_pow_p_mul`: the existence of this element `b` over a perfect ring
* `WittVector.exists_eq_pow_p_mul'`: the existence of this unit `b` over a perfect field
* `WittVector.isDiscreteValuationRing`: `𝕎 k` is a discrete valuation ring if `k` is a perfect field

-/

noncomputable section

namespace WittVector

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝕎" => WittVector p

section CommRing

variable {k : Type*} [CommRing k] [CharP k p]

def succNthValUnits (n : ℕ) (a : Units k) (A : 𝕎 k) (bs : Fin (n + 1) → k) : k :=
  -↑(a⁻¹ ^ p ^ (n + 1)) *
    (A.coeff (n + 1) * ↑(a⁻¹ ^ p ^ (n + 1)) + nthRemainder p n (truncateFun (n + 1) A) bs)

noncomputable def inverseCoeff (a : Units k) (A : 𝕎 k) : ℕ → k
  | 0 => ↑a⁻¹
  | n + 1 => succNthValUnits n a A fun i => inverseCoeff a A i.val

def mkUnit {a : Units k} {A : 𝕎 k} (hA : A.coeff 0 = a) : Units (𝕎 k) :=
  Units.mkOfMulEqOne A (@WittVector.mk' p _ (inverseCoeff a A)) (by
    ext n
    induction n with
    | zero => simp [WittVector.mul_coeff_zero, inverseCoeff, hA]
    | succ n => ?_
    let H_coeff := A.coeff (n + 1) * ↑(a⁻¹ ^ p ^ (n + 1)) +
      nthRemainder p n (truncateFun (n + 1) A) fun i : Fin (n + 1) => inverseCoeff a A i
    have H := Units.mul_inv (a ^ p ^ (n + 1))
    linear_combination (norm := skip) -H_coeff * H
    have ha : (a : k) ^ p ^ (n + 1) = ↑(a ^ p ^ (n + 1)) := by norm_cast
    have ha_inv : (↑a⁻¹ : k) ^ p ^ (n + 1) = ↑(a ^ p ^ (n + 1))⁻¹ := by norm_cast
    simp only [nthRemainder_spec, inverseCoeff, succNthValUnits, hA,
      one_coeff_eq_of_pos, Nat.succ_pos', ha_inv, ha, inv_pow]
    ring!)
