/-
Extracted from Algebra/MvPolynomial/Derivation.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Derivations of multivariate polynomials

In this file we prove that a derivation of `MvPolynomial σ R` is determined by its values on all
monomials `MvPolynomial.X i`. We also provide a constructor `MvPolynomial.mkDerivation` that
builds a derivation from its values on `X i`s and a linear equivalence
`MvPolynomial.mkDerivationEquiv` between `σ → A` and `Derivation (MvPolynomial σ R) A`.
-/

namespace MvPolynomial

noncomputable section

variable {σ R A : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A]
  [Module (MvPolynomial σ R) A]

variable (R)

def mkDerivationₗ (f : σ → A) : MvPolynomial σ R →ₗ[R] A :=
  Finsupp.lsum R fun xs : σ →₀ ℕ =>
    (LinearMap.ringLmapEquivSelf R R A).symm <|
      xs.sum fun i k => monomial (xs - Finsupp.single i 1) (k : R) • f i

end

theorem mkDerivationₗ_monomial (f : σ → A) (s : σ →₀ ℕ) (r : R) :
    mkDerivationₗ R f (monomial s r) =
      r • s.sum fun i k => monomial (s - Finsupp.single i 1) (k : R) • f i :=
  sum_monomial_eq <| map_zero _

theorem mkDerivationₗ_C (f : σ → A) (r : R) : mkDerivationₗ R f (C r) = 0 :=
  (mkDerivationₗ_monomial f _ _).trans (smul_zero _)

theorem mkDerivationₗ_X (f : σ → A) (i : σ) : mkDerivationₗ R f (X i) = f i :=
  (mkDerivationₗ_monomial f _ _).trans <| by simp [tsub_self]
