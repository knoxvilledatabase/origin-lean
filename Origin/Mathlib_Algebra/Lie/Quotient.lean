/-
Extracted from Algebra/Lie/Quotient.lean
Genuine: 1 of 7 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core

/-!
# Quotients of Lie algebras and Lie modules

Given a Lie submodule of a Lie module, the quotient carries a natural Lie module structure. In the
special case that the Lie module is the Lie algebra itself via the adjoint action, the submodule
is a Lie ideal and the quotient carries a natural Lie algebra structure.

We define these quotient structures here. A notable omission at the time of writing (February 2021)
is a statement and proof of the universal property of these quotients.

## Main definitions

  * `LieSubmodule.Quotient.lieQuotientLieModule`
  * `LieSubmodule.Quotient.lieQuotientLieAlgebra`

## Tags

lie algebra, quotient
-/

universe u v w w₁ w₂

namespace LieSubmodule

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (N N' : LieSubmodule R L M)

-- INSTANCE (free from Core): :

namespace Quotient

variable {N}

-- INSTANCE (free from Core): addCommGroup

-- INSTANCE (free from Core): module'

-- INSTANCE (free from Core): module

-- INSTANCE (free from Core): isCentralScalar

-- INSTANCE (free from Core): inhabited

abbrev mk : M → M ⧸ N :=
  Submodule.Quotient.mk
