/-
Extracted from Algebra/Module/LocalizedModule/AtPrime.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Localizations of modules at the complement of a prime ideal
-/

protected abbrev IsLocalizedModule.AtPrime {R M M' : Type*} [CommSemiring R] (P : Ideal R)
    [P.IsPrime] [AddCommMonoid M] [AddCommMonoid M'] [Module R M] [Module R M'] (f : M →ₗ[R] M') :=
  IsLocalizedModule P.primeCompl f

protected abbrev LocalizedModule.AtPrime {R : Type*} [CommSemiring R] (P : Ideal R) [P.IsPrime]
    (M : Type*) [AddCommMonoid M] [Module R M] :=
  LocalizedModule P.primeCompl M
