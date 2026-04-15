/-
Extracted from RepresentationTheory/Submodule.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Invariant submodules of a group representation

-/

open scoped MonoidAlgebra

variable {k G V : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]
  (ρ : Representation k G V)

namespace Representation

def invtSubmodule : Sublattice (Submodule k V) :=
  ⨅ g, Module.End.invtSubmodule (ρ g)

lemma mem_invtSubmodule {p : Submodule k V} :
    p ∈ ρ.invtSubmodule ↔ ∀ g, p ∈ Module.End.invtSubmodule (ρ g) := by
  rw [invtSubmodule, Sublattice.mem_iInf]

namespace invtSubmodule
