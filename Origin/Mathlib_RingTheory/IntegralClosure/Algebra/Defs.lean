/-
Extracted from RingTheory/IntegralClosure/Algebra/Defs.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs

/-!
# Integral algebras

## Main definitions

Let `R` be a `CommRing` and let `A` be an R-algebra.

* `Algebra.IsIntegral R A` : An algebra is integral if every element of the extension is integral
  over the base ring.
-/

open Polynomial Submodule

section Ring

variable {R S A : Type*}

variable [CommRing R] [Ring A] [Ring S] (f : R →+* S)

variable [Algebra R A] (R)

variable (A)

protected class Algebra.IsIntegral : Prop where
  isIntegral : ∀ x : A, IsIntegral R x

variable {R A}

lemma Algebra.isIntegral_def : Algebra.IsIntegral R A ↔ ∀ x : A, IsIntegral R x :=
  ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩

end Ring
