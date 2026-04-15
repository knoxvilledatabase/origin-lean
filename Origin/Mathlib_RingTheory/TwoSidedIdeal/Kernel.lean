/-
Extracted from RingTheory/TwoSidedIdeal/Kernel.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Kernel of a ring homomorphism as a two-sided ideal

In this file we define the kernel of a ring homomorphism `f : R → S` as a two-sided ideal of `R`.

We put this in a separate file so that we could import it in
`Mathlib/RingTheory/SimpleRing/Basic.lean` without importing any finiteness result.
-/

assert_not_exists Finset

namespace TwoSidedIdeal

section ker

variable {R S : Type*} [NonUnitalNonAssocRing R] [NonUnitalNonAssocSemiring S]

variable {F : Type*} [FunLike F R S] [NonUnitalRingHomClass F R S]

variable (f : F)

def ker : TwoSidedIdeal R :=
  .mk
  { r := fun x y ↦ f x = f y
    iseqv := by constructor <;> aesop
    mul' := by intro; simp_all
    add' := by intro; simp_all }
