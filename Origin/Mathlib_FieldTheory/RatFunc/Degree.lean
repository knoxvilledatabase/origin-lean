/-
Extracted from FieldTheory/RatFunc/Degree.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The degree of rational functions

## Main definitions
We define the degree of a rational function, with values in `ℤ`:
- `intDegree` is the degree of a rational function, defined as the difference between the
  `natDegree` of its numerator and the `natDegree` of its denominator. In particular,
  `intDegree 0 = 0`.
-/

noncomputable section

universe u

variable {K : Type u}

namespace RatFunc

section IntDegree

open Polynomial

variable [Field K]

def intDegree (x : K⟮X⟯) : ℤ :=
  natDegree x.num - natDegree x.denom
