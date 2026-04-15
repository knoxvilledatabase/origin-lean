/-
Extracted from LinearAlgebra/Quotient/Pi.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Submodule quotients and direct sums

This file contains some results on the quotient of a module by a direct sum of submodules,
and the direct sum of quotients of modules by submodules.

## Main definitions

* `Submodule.piQuotientLift`: create a map out of the direct sum of quotients
* `Submodule.quotientPiLift`: create a map out of the quotient of a direct sum
* `Submodule.quotientPi`: the quotient of a direct sum is the direct sum of quotients.

-/

namespace Submodule

open LinearMap

variable {ι R : Type*} [CommRing R]

variable {Ms : ι → Type*} [∀ i, AddCommGroup (Ms i)] [∀ i, Module R (Ms i)]

variable {N : Type*} [AddCommGroup N] [Module R N]

variable {Ns : ι → Type*} [∀ i, AddCommGroup (Ns i)] [∀ i, Module R (Ns i)]

def piQuotientLift [Fintype ι] [DecidableEq ι] (p : ∀ i, Submodule R (Ms i)) (q : Submodule R N)
    (f : ∀ i, Ms i →ₗ[R] N) (hf : ∀ i, p i ≤ q.comap (f i)) : (∀ i, Ms i ⧸ p i) →ₗ[R] N ⧸ q :=
  lsum R (fun i => Ms i ⧸ p i) R fun i => (p i).mapQ q (f i) (hf i)
