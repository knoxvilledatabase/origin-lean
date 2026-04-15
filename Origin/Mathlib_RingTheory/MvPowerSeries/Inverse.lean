/-
Extracted from RingTheory/MvPowerSeries/Inverse.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Formal (multivariate) power series - Inverses

This file defines multivariate formal power series and develops the basic
properties of these objects, when it comes about multiplicative inverses.

For `φ : MvPowerSeries σ R` and `u : Rˣ` is the constant coefficient of `φ`,
`MvPowerSeries.invOfUnit φ u` is a formal power series such,
and `MvPowerSeries.mul_invOfUnit` proves that `φ * invOfUnit φ u = 1`.
The construction of the power series `invOfUnit` is done by writing that
relation and solving and for its coefficients by induction.

Over a field, all power series `φ` have an “inverse” `MvPowerSeries.inv φ`,
which is `0` if and only if the constant coefficient of `φ` is zero
(by `MvPowerSeries.inv_eq_zero`),
and `MvPowerSeries.mul_inv_cancel` asserts the equality `φ * φ⁻¹ = 1` when
the constant coefficient of `φ` is nonzero.

Instances are defined:

* Formal power series over a local ring form a local ring.
* The morphism `MvPowerSeries.map σ f : MvPowerSeries σ A →* MvPowerSeries σ B`
  induced by a local morphism `f : A →+* B` (`IsLocalHom f`)
  of commutative rings is a *local* morphism.

-/

noncomputable section

open Finset (antidiagonal mem_antidiagonal)

namespace MvPowerSeries

open Finsupp

variable {σ R : Type*}

section Ring

variable [Ring R]

protected noncomputable def inv.aux (a : R) (φ : MvPowerSeries σ R) : MvPowerSeries σ R
  | n =>
    letI := Classical.decEq σ
    if n = 0 then a
    else
      -a *
        ∑ x ∈ antidiagonal n, if _ : x.2 < n then coeff x.1 φ * inv.aux a φ x.2 else 0

termination_by n => n

theorem coeff_inv_aux [DecidableEq σ] (n : σ →₀ ℕ) (a : R) (φ : MvPowerSeries σ R) :
    coeff n (inv.aux a φ) =
      if n = 0 then a
      else
        -a *
          ∑ x ∈ antidiagonal n, if x.2 < n then coeff x.1 φ * coeff x.2 (inv.aux a φ) else 0 :=
  show inv.aux a φ n = _ by
    cases Subsingleton.elim ‹DecidableEq σ› (Classical.decEq σ)
    rw [inv.aux]
    rfl

def invOfUnit (φ : MvPowerSeries σ R) (u : Rˣ) : MvPowerSeries σ R :=
  inv.aux (↑u⁻¹) φ

theorem coeff_invOfUnit [DecidableEq σ] (n : σ →₀ ℕ) (φ : MvPowerSeries σ R) (u : Rˣ) :
    coeff n (invOfUnit φ u) =
      if n = 0 then ↑u⁻¹
      else
        -↑u⁻¹ *
          ∑ x ∈ antidiagonal n,
            if x.2 < n then coeff x.1 φ * coeff x.2 (invOfUnit φ u) else 0 := by
  convert coeff_inv_aux n (↑u⁻¹) φ
