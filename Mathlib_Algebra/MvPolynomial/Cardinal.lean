/-
Extracted from Algebra/MvPolynomial/Cardinal.lean
Genuine: 3 | Conflates: 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Data.Finsupp.Fintype
import Mathlib.SetTheory.Cardinal.Finsupp

noncomputable section

/-!
# Cardinality of Multivariate Polynomial Ring

The main result in this file is `MvPolynomial.cardinalMk_le_max`, which says that
the cardinality of `MvPolynomial σ R` is bounded above by the maximum of `#R`, `#σ`
and `ℵ₀`.
-/

universe u v

open Cardinal

namespace MvPolynomial

section TwoUniverses

variable {σ : Type u} {R : Type v} [CommSemiring R]

-- CONFLATES (assumes ground = zero): cardinalMk_eq_max_lift
@[simp]
theorem cardinalMk_eq_max_lift [Nonempty σ] [Nontrivial R] :
    #(MvPolynomial σ R) = max (max (Cardinal.lift.{u} #R) <| Cardinal.lift.{v} #σ) ℵ₀ :=
  (mk_finsupp_lift_of_infinite _ R).trans <| by
    rw [mk_finsupp_nat, max_assoc, lift_max, lift_aleph0, max_comm]

@[simp]
theorem cardinalMk_eq_lift [IsEmpty σ] : #(MvPolynomial σ R) = Cardinal.lift.{u} #R :=
  ((isEmptyRingEquiv R σ).toEquiv.trans Equiv.ulift.{u}.symm).cardinal_eq

-- CONFLATES (assumes ground = zero): cardinalMk_eq_one
@[nontriviality]
theorem cardinalMk_eq_one [Subsingleton R] : #(MvPolynomial σ R) = 1 := mk_eq_one _

theorem cardinalMk_le_max_lift {σ : Type u} {R : Type v} [CommSemiring R] : #(MvPolynomial σ R) ≤
    max (max (Cardinal.lift.{u} #R) <| Cardinal.lift.{v} #σ) ℵ₀ := by
  cases subsingleton_or_nontrivial R
  · exact (mk_eq_one _).trans_le (le_max_of_le_right one_le_aleph0)
  cases isEmpty_or_nonempty σ
  · exact cardinalMk_eq_lift.trans_le (le_max_of_le_left <| le_max_left _ _)
  · exact cardinalMk_eq_max_lift.le

end TwoUniverses

variable {σ R : Type u} [CommSemiring R]

-- CONFLATES (assumes ground = zero): cardinalMk_eq_max
theorem cardinalMk_eq_max [Nonempty σ] [Nontrivial R] :
    #(MvPolynomial σ R) = max (max #R #σ) ℵ₀ := by simp

theorem cardinalMk_le_max : #(MvPolynomial σ R) ≤ max (max #R #σ) ℵ₀ :=
  cardinalMk_le_max_lift.trans <| by rw [lift_id, lift_id]

end MvPolynomial
