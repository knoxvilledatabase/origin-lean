/-
Extracted from Algebra/Star/SelfAdjoint.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Self-adjoint, skew-adjoint and normal elements of a star additive group

This file defines `selfAdjoint R` (resp. `skewAdjoint R`), where `R` is a star additive group,
as the additive subgroup containing the elements that satisfy `star x = x` (resp. `star x = -x`).
This includes, for instance, (skew-)Hermitian operators on Hilbert spaces.

We also define `IsStarNormal R`, a `Prop` that states that an element `x` satisfies
`star x * x = x * star x`.

## Implementation notes

* When `R` is a `StarModule R₂ R`, then `selfAdjoint R` has a natural
  `Module (selfAdjoint R₂) (selfAdjoint R)` structure. However, doing this literally would be
  undesirable since in the main case of interest (`R₂ = ℂ`) we want `Module ℝ (selfAdjoint R)`
  and not `Module (selfAdjoint ℂ) (selfAdjoint R)`. We solve this issue by adding the typeclass
  `[TrivialStar R₃]`, of which `ℝ` is an instance (registered in `Data/Real/Basic`), and then
  add a `[Module R₃ (selfAdjoint R)]` instance whenever we have
  `[Module R₃ R] [TrivialStar R₃]`. (Another approach would have been to define
  `[StarInvariantScalars R₃ R]` to express the fact that `star (x • v) = x • star v`, but
  this typeclass would have the disadvantage of taking two type arguments.)

## TODO

* Define `IsSkewAdjoint` to match `IsSelfAdjoint`.
* Define `fun z x => z * x * star z` (i.e. conjugation by `z`) as a monoid action of `R` on `R`
  (similar to the existing `ConjAct` for groups), and then state the fact that `selfAdjoint R` is
  invariant under it.

-/

open Function

variable {R A : Type*}

def IsSelfAdjoint [Star R] (x : R) : Prop :=
  star x = x
