/-
Extracted from RingTheory/Etale/StandardEtale.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Standard etale maps

## Main definitions
- `StandardEtalePair`:
  A pair `f g : R[X]` such that `f` is monic and `f'` is invertible in `R[X][1/g]`.
- `StandardEtalePair`: The standard etale algebra corresponding to a `StandardEtalePair`.
- `StandardEtalePair.equivPolynomialQuotient`   : `P.Ring ≃ R[X][Y]/⟨f, Yg-1⟩`
- `StandardEtalePair.equivAwayAdjoinRoot`       : `P.Ring ≃ (R[X]/f)[1/g]`
- `StandardEtalePair.equivAwayQuotient`         : `P.Ring ≃ R[X][1/g]/f`
- `StandardEtalePair.equivMvPolynomialQuotient` : `P.Ring ≃ R[X, Y]/⟨f, Yg-1⟩`
- `StandardEtalePair.homEquiv`:
  Maps out of `P.Ring` corresponds to `x` such that `f(x) = 0` and `g(x)` is invertible.
- We also provide the instance that `P.Ring` is etale over `R`.

- `Algebra.IsStandardEtale`: The class of standard etale algebras.

-/

universe u

open Polynomial

open scoped Bivariate

noncomputable section

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

variable (R) in

structure StandardEtalePair : Type _ where
  /-- The monic polynomial to be quotiented out in a standard etale algebra. -/
  f : R[X]
  monic_f : f.Monic
  /-- The polynomial to be localized away from in a standard etale algebra. -/
  g : R[X]
  cond : ∃ p₁ p₂ n, derivative f * p₁ + f * p₂ = g ^ n

variable (P : StandardEtalePair R)

protected def StandardEtalePair.Ring := R[X][Y] ⧸ Ideal.span {C P.f, Y * C P.g - 1}
  deriving CommRing, Algebra R

namespace StandardEtalePair

protected def X : P.Ring := Ideal.Quotient.mk _ (C .X)

def HasMap (x : S) : Prop :=
  aeval x P.f = 0 ∧ IsUnit (aeval x P.g)

def lift (x : S) (h : P.HasMap x) : P.Ring →ₐ[R] S :=
  Ideal.Quotient.liftₐ _ (aevalAeval x ↑(h.2.unit⁻¹))
    (Ideal.span_le (I := RingHom.ker _).mpr (by simp [Set.pair_subset_iff, h.1]))

set_option backward.isDefEq.respectTransparency false in
