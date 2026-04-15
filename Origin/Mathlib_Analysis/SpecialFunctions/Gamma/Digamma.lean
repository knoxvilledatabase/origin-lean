/-
Extracted from Analysis/SpecialFunctions/Gamma/Digamma.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# The digamma function

This file defines the digamma function as the logarithmic derivative of the Gamma function and
proves some basic properties.

## Main definitions

* `Complex.digamma`: The digamma function of a complex variable.

## Main statements

* `Complex.digamma_apply_add_one`: The digamma function satisfies the functional equation
  `digamma (s + 1) = digamma s + s⁻¹`.
* `Complex.meromorphic_digamma`: The digamma function is meromorphic.

## TODO

* Prove Gauss' integral representation of the digamma function.
-/

namespace Complex

noncomputable def digamma : ℂ → ℂ := logDeriv Gamma
