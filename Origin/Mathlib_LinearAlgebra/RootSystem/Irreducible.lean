/-
Extracted from LinearAlgebra/RootSystem/Irreducible.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Irreducible root pairings

This file contains basic definitions and results about irreducible root systems.

## Main definitions / results:
* `RootPairing.isSimpleModule_weylGroupRootRep_iff`: a criterion for the representation of the Weyl
  group on root space to be irreducible.
* `RootPairing.IsIrreducible`: a typeclass encoding the fact that a root pairing is irreducible.
* `RootPairing.IsIrreducible.mk'`: an alternative constructor for irreducibility when the
  coefficients are a field.

-/

open Function Set

open Submodule (span span_le)

open LinearMap (ker)

open MulAction (orbit mem_orbit_self mem_orbit_iff)

open Module.End (invtSubmodule)

open scoped MonoidAlgebra

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N)

namespace RootPairing

def invtRootSubmodule : Sublattice (Submodule R M) :=
  ⨅ i, invtSubmodule (P.reflection i)

lemma mem_invtRootSubmodule_iff {q : Submodule R M} :
    q ∈ P.invtRootSubmodule ↔ ∀ i, q ∈ Module.End.invtSubmodule (P.reflection i) := by
  simp [invtRootSubmodule]
