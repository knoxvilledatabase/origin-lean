/-
Extracted from Algebra/Lie/Submodule.lean
Genuine: 1 of 10 | Dissolved: 0 | Infrastructure: 9
-/
import Origin.Core

/-!
# Lie submodules of a Lie algebra

In this file we define Lie submodules, we construct the lattice structure on Lie submodules and we
use it to define various important operations, notably the Lie span of a subset of a Lie module.

## Main definitions

  * `LieSubmodule`
  * `LieSubmodule.wellFounded_of_noetherian`
  * `LieSubmodule.lieSpan`
  * `LieSubmodule.map`
  * `LieSubmodule.comap`

## Tags

lie algebra, lie submodule, lie ideal, lattice structure
-/

universe u v w w₁ w₂

section LieSubmodule

variable (R : Type u) (L : Type v) (M : Type w)

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

structure LieSubmodule extends Submodule R M where
  lie_mem : ∀ {x : L} {m : M}, m ∈ carrier → ⁅x, m⁆ ∈ carrier

attribute [nolint docBlame] LieSubmodule.toSubmodule

attribute [coe] LieSubmodule.toSubmodule

namespace LieSubmodule

variable {R L M}

variable (N N' : LieSubmodule R L M)

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): instSMulMemClass

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): :
