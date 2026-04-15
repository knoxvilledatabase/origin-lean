/-
Extracted from RingTheory/Derivation/ToSquareZero.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Derivations into Square-Zero Ideals

## Main statements

- `derivationToSquareZeroOfLift`: The `R`-derivations from `A` into a square-zero ideal `I`
  of `B` corresponds to the lifts `A →ₐ[R] B` of the map `A →ₐ[R] B ⧸ I`.

-/

section ToSquareZero

universe u v w

variable {R : Type u} {A : Type v} {B : Type w} [CommSemiring R] [CommSemiring A] [CommRing B]

variable [Algebra R A] [Algebra R B] (I : Ideal B)

def diffToIdealOfQuotientCompEq (f₁ f₂ : A →ₐ[R] B)
    (e : (Ideal.Quotient.mkₐ R I).comp f₁ = (Ideal.Quotient.mkₐ R I).comp f₂) : A →ₗ[R] I :=
  LinearMap.codRestrict (I.restrictScalars _) (f₁.toLinearMap - f₂.toLinearMap)
    (fun x => by simpa [Ideal.Quotient.eq] using congr($e x))
