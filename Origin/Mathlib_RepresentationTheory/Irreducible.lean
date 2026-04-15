/-
Extracted from RepresentationTheory/Irreducible.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Irreducible representations

This file defines irreducible monoid representations.

-/

namespace Representation

open scoped MonoidAlgebra

variable {G k V W : Type*} [Monoid G] [Field k] [AddCommGroup V] [Module k V] [AddCommGroup W]
    [Module k W] (ρ : Representation k G V) (σ : Representation k G W)

abbrev IsIrreducible :=
  IsSimpleOrder (Subrepresentation ρ)

set_option backward.isDefEq.respectTransparency false in

theorem irreducible_iff_isSimpleModule_asModule :
    IsIrreducible ρ ↔ IsSimpleModule k[G] ρ.asModule := by
  rw [isSimpleModule_iff]
  exact OrderIso.isSimpleOrder_iff Subrepresentation.subrepresentationSubmoduleOrderIso

set_option backward.isDefEq.respectTransparency false in

theorem isSimpleModule_iff_irreducible_ofModule (M : Type*) [AddCommGroup M] [Module k[G] M] :
    IsSimpleModule k[G] M ↔ IsIrreducible (ofModule (k := k) (G := G) M) := by
  rw [isSimpleModule_iff]
  exact OrderIso.isSimpleOrder_iff Subrepresentation.submoduleSubrepresentationOrderIso
