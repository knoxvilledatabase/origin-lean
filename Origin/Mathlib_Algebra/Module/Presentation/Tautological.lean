/-
Extracted from Algebra/Module/Presentation/Tautological.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The tautological presentation of a module

Given an `A`-module `M`, we provide its tautological presentation:
* there is a generator `[m]` for each `m : M`;
* the relations are `[m₁] + [m₂] - [m₁ + m₂] = 0` and `a • [m] - [a • m] = 0`.

-/

universe w v u

namespace Module

variable (A : Type u) [Ring A] (M : Type v) [AddCommGroup M] [Module A M]

namespace Presentation

inductive tautological.R
  | add (m₁ m₂ : M)
  | smul (a : A) (m : M)
