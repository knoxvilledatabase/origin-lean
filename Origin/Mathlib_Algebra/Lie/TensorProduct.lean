/-
Extracted from Algebra/Lie/TensorProduct.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Tensor products of Lie modules

Tensor products of Lie modules carry natural Lie module structures.

## Tags

lie module, tensor product, universal property
-/

universe u v w w₁ w₂ w₃

variable {R : Type u} [CommRing R]

open LieModule

namespace TensorProduct

open scoped TensorProduct

namespace LieModule

variable {L : Type v} {M : Type w} {N : Type w₁} {P : Type w₂} {Q : Type w₃}

variable [LieRing L] [LieAlgebra R L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]

variable [AddCommGroup P] [Module R P] [LieRingModule L P] [LieModule R L P]

variable [AddCommGroup Q] [Module R Q] [LieRingModule L Q] [LieModule R L Q]

attribute [local ext] TensorProduct.ext

def hasBracketAux (x : L) : Module.End R (M ⊗[R] N) :=
  (toEnd R L M x).rTensor N + (toEnd R L N x).lTensor M

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): lieRingModule

-- INSTANCE (free from Core): lieModule
