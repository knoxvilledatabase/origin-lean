/-
Extracted from RingTheory/PowerSeries/Inverse.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Formal power series - Inverses

If the constant coefficient of a formal (univariate) power series is invertible,
then this formal power series is invertible.
(See the discussion in `Mathlib/RingTheory/MvPowerSeries/Inverse.lean` for
the construction.)

Formal (univariate) power series over a local ring form a local ring.

Formal (univariate) power series over a field form a discrete valuation ring, and a normalization
monoid. The definition `residueFieldOfPowerSeries` provides the isomorphism between the residue
field of `k⟦X⟧` and `k`, when `k` is a field.

-/

noncomputable section

open Polynomial

open Finset (antidiagonal mem_antidiagonal)

namespace PowerSeries

open Finsupp (single)

variable {R : Type*}

section Ring

variable [Ring R]

protected def inv.aux : R → R⟦X⟧ → R⟦X⟧ :=
  MvPowerSeries.inv.aux

theorem coeff_inv_aux (n : ℕ) (a : R) (φ : R⟦X⟧) :
    coeff n (inv.aux a φ) =
      if n = 0 then a
      else
        -a *
          ∑ x ∈ antidiagonal n,
            if x.2 < n then coeff x.1 φ * coeff x.2 (inv.aux a φ) else 0 := by
  rw [coeff, inv.aux, MvPowerSeries.coeff_inv_aux]
  simp only [Finsupp.single_eq_zero]
  split_ifs; · rfl
  congr 1
  symm
  apply Finset.sum_nbij' (fun (a, b) ↦ (single () a, single () b))
    fun (f, g) ↦ (f (), g ())
  · aesop
  · aesop
  · aesop
  · aesop
  · rintro ⟨i, j⟩ _hij
    obtain H | H := le_or_gt n j
    · aesop
    rw [if_pos H, if_pos]
    · rfl
    refine ⟨?_, fun hh ↦ H.not_ge ?_⟩
    · rintro ⟨⟩
      simpa [Finsupp.single_eq_same] using le_of_lt H
    · simpa [Finsupp.single_eq_same] using hh ()

def invOfUnit (φ : R⟦X⟧) (u : Rˣ) : R⟦X⟧ :=
  MvPowerSeries.invOfUnit φ u

theorem coeff_invOfUnit (n : ℕ) (φ : R⟦X⟧) (u : Rˣ) :
    coeff n (invOfUnit φ u) =
      if n = 0 then ↑u⁻¹
      else
        -↑u⁻¹ *
          ∑ x ∈ antidiagonal n,
            if x.2 < n then coeff x.1 φ * coeff x.2 (invOfUnit φ u) else 0 :=
  coeff_inv_aux n (↑u⁻¹ : R) φ
