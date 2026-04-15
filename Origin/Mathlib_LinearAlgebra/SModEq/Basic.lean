/-
Extracted from LinearAlgebra/SModEq/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# modular equivalence for submodule
-/

open Submodule

open Polynomial

variable {R : Type*} [Ring R]

variable {S : Type*} [Ring S]

variable {A : Type*} [CommRing A]

variable {M : Type*} [AddCommGroup M] [Module R M] [Module S M] (U U₁ U₂ : Submodule R M)

variable {x x₁ x₂ y y₁ y₂ z z₁ z₂ : M}

variable {N : Type*} [AddCommGroup N] [Module R N] (V V₁ V₂ : Submodule R N)

def SModEq (x y : M) : Prop :=
  (Submodule.Quotient.mk x : M ⧸ U) = Submodule.Quotient.mk y
