/-
Extracted from RepresentationTheory/Semisimple.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Semisimple representations

This file defines the typeclass `IsSemisimpleRepresentation` for semisimple monoid representations.

-/

namespace Representation

variable {k G V : Type*}

open scoped MonoidAlgebra

variable [Monoid G] [Field k] [AddCommGroup V] [Module k V]
  (ρ : Representation k G V)

abbrev IsSemisimpleRepresentation :=
  ComplementedLattice (Subrepresentation ρ)

set_option backward.isDefEq.respectTransparency false in

theorem isSemisimpleRepresentation_iff_isSemisimpleModule_asModule :
    IsSemisimpleRepresentation ρ ↔ IsSemisimpleModule k[G] ρ.asModule := by
  rw [isSemisimpleModule_iff]
  exact OrderIso.complementedLattice_iff Subrepresentation.subrepresentationSubmoduleOrderIso

set_option backward.isDefEq.respectTransparency false in

theorem isSemisimpleModule_iff_isSemisimpleRepresentation_ofModule (M : Type*) [AddCommGroup M]
    [Module k[G] M] :
    IsSemisimpleModule k[G] M ↔ IsSemisimpleRepresentation (ofModule (k := k) (G := G) M) := by
  rw [isSemisimpleModule_iff]
  exact OrderIso.complementedLattice_iff Subrepresentation.submoduleSubrepresentationOrderIso

end

end Representation
