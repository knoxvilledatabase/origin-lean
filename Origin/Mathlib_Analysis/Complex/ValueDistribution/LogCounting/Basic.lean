/-
Extracted from Analysis/Complex/ValueDistribution/LogCounting/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The Logarithmic Counting Function of Value Distribution Theory

For nontrivially normed fields `𝕜`, this file defines the logarithmic counting function of a
meromorphic function defined on `𝕜`.  Also known as the `Nevanlinna counting function`, this is one
of the three main functions used in Value Distribution Theory.

The logarithmic counting function of a meromorphic function `f` is a logarithmically weighted
measure of the number of times the function `f` takes a given value `a` within the disk `∣z∣ ≤ r`,
taking multiplicities into account.

See Section VI.1 of [Lang, *Introduction to Complex Hyperbolic Spaces*][MR886677] or Section 1.1 of
[Noguchi-Winkelmann, *Nevanlinna Theory in Several Complex Variables and Diophantine
Approximation*][MR3156076] for a detailed discussion.

## Implementation Notes

- This file defines the logarithmic counting function first for functions with locally finite
  support on `𝕜` and then specializes to the setting where the function with locally finite support
  is the pole or zero-divisor of a meromorphic function.

- Even though value distribution theory is best developed for meromorphic functions on the complex
  plane (and therefore placed in the complex analysis section of Mathlib), we introduce the
  logarithmic counting function for arbitrary normed fields.

## TODO

- Discuss the logarithmic counting function for rational functions, add a forward reference to the
  upcoming converse, formulated in terms of the Nevanlinna height.
-/

open Filter Function MeromorphicOn Metric Real Set

/-!
## Supporting Notation
-/

namespace Function.locallyFinsuppWithin

variable {E : Type*} [NormedAddCommGroup E]

noncomputable def toClosedBall (r : ℝ) :
    locallyFinsupp E ℤ →+ locallyFinsuppWithin (closedBall (0 : E) |r|) ℤ := by
  apply restrictMonoidHom
  tauto
