/-
Extracted from Algebra/Module/LocalizedModule/Away.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Localizations of modules away from an element
-/

protected abbrev IsLocalizedModule.Away {R M M' : Type*} [CommSemiring R] (x : R) [AddCommMonoid M]
    [Module R M] [AddCommMonoid M'] [Module R M'] (f : M →ₗ[R] M') :=
  IsLocalizedModule (Submonoid.powers x) f

protected abbrev LocalizedModule.Away {R : Type*} [CommSemiring R] (x : R)
    (M : Type*) [AddCommMonoid M] [Module R M] :=
  LocalizedModule (Submonoid.powers x) M
