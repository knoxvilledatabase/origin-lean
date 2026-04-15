/-
Extracted from LinearAlgebra/RootSystem/CartanMatrix.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Cartan matrices for root systems

This file contains definitions and basic results about Cartan matrices of root pairings / systems.

## Main definitions:
* `RootPairing.Base.cartanMatrix`: the Cartan matrix of a crystallographic root pairing, with
  respect to a base `b`.
* `RootPairing.Base.cartanMatrix_nondegenerate`: the Cartan matrix is non-degenerate.
* `RootPairing.Base.induction_on_cartanMatrix`: an induction principle expressing the connectedness
  of the Dynkin diagram of an irreducible root pairing.
* `RootPairing.Base.equivOfCartanMatrixEq`: a root system is determined by its Cartan matrix.

-/

noncomputable section

open FaithfulSMul (algebraMap_injective)

open Function Set

open Module.End (invtSubmodule mem_invtSubmodule)

open Submodule (span subset_span)

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

namespace RootPairing.Base

variable (S : Type*) [CommRing S] [Algebra S R]
  {P : RootPairing ι R M N} [P.IsValuedIn S] (b : P.Base)

def cartanMatrixIn :
    Matrix b.support b.support S :=
  .of fun i j ↦ P.pairingIn S i j
