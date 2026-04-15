/-
Extracted from FieldTheory/IntermediateField/Adjoin/Algebra.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Adjoining Elements to Fields

This file relates `IntermediateField.adjoin` to `Algebra.adjoin`.
-/

open Module Polynomial

namespace IntermediateField

section AdjoinDef

variable (F : Type*) [Field F] {E : Type*} [Field E] [Algebra F E] (S : Set E)

theorem algebra_adjoin_le_adjoin : Algebra.adjoin F S ≤ (adjoin F S).toSubalgebra :=
  Algebra.adjoin_le (subset_adjoin _ _)

namespace algebraAdjoinAdjoin

-- INSTANCE (free from Core): :
