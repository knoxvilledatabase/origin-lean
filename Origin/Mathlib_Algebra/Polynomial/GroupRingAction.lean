/-
Extracted from Algebra/Polynomial/GroupRingAction.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Group action on rings applied to polynomials

This file contains instances and definitions relating `MulSemiringAction` to `Polynomial`.
-/

variable (M : Type*) [Monoid M]

open Polynomial

namespace Polynomial

variable (R : Type*) [Semiring R]

variable {M} in

theorem smul_eq_map [MulSemiringAction M R] (m : M) :
    HSMul.hSMul m = map (MulSemiringAction.toRingHom M R m) := by
  ext
  simp

-- INSTANCE (free from Core): [MulSemiringAction

variable {M R}

variable [MulSemiringAction M R]
