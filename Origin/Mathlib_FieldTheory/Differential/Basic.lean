/-
Extracted from FieldTheory/Differential/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Differential Fields

This file defines the logarithmic derivative `Differential.logDeriv` and proves properties of it.
This is defined algebraically, compared to `logDeriv` which is analytical.
-/

namespace Differential

open algebraMap Polynomial IntermediateField

variable {R : Type*} [Field R] [Differential R] (a b : R)

def logDeriv : R := a′ / a
