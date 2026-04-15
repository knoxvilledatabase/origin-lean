/-
Extracted from Algebra/Lie/Nilpotent.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Nilpotent Lie algebras

Like groups, Lie algebras admit a natural concept of nilpotency. More generally, any Lie module
carries a natural concept of nilpotency. We define these here via the lower central series.

## Main definitions

  * `LieModule.lowerCentralSeries`
  * `LieModule.IsNilpotent`
  * `LieModule.maxNilpotentSubmodule`
  * `LieAlgebra.maxNilpotentIdeal`

## Tags

lie algebra, lower central series, nilpotent, max nilpotent ideal
-/

universe u v w w₁ w₂

section NilpotentModules

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (k : ℕ) (N : LieSubmodule R L M)

namespace LieSubmodule

def lcs : LieSubmodule R L M → LieSubmodule R L M :=
  (fun N => ⁅(⊤ : LieIdeal R L), N⁆)^[k]
