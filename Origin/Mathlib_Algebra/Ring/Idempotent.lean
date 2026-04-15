/-
Extracted from Algebra/Ring/Idempotent.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Idempotent elements of a ring

This file proves result about idempotent elements of a ring, like:
* `IsIdempotentElem.one_sub_iff`: In a (non-associative) ring, `a` is an idempotent if and only if
  `1 - a` is an idempotent.
-/

variable {R : Type*}

namespace IsIdempotentElem

section NonAssocRing

variable [NonAssocRing R] {a : R}

lemma one_sub (h : IsIdempotentElem a) : IsIdempotentElem (1 - a) := by
  rw [IsIdempotentElem, mul_sub, mul_one, sub_mul, one_mul, h.eq, sub_self, sub_zero]
