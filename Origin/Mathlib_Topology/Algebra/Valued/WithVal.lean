/-
Extracted from Topology/Algebra/Valued/WithVal.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Ring topologised by a valuation

For a given valuation `v : Valuation R Γ₀` on a ring `R` taking values in `Γ₀`, this file
defines the type synonym `WithVal v` of `R`. By assigning a `Valued (WithVal v) Γ₀` instance,
`WithVal v` represents the ring `R` equipped with the topology coming from `v`. The type
synonym `WithVal v` is in isomorphism to `R` as rings via `WithVal.equiv v`. This
isomorphism should be used to explicitly map terms of `WithVal v` to terms of `R`.

The `WithVal` type synonym is used to define the completion of `R` with respect to `v` in
`Valuation.Completion`. An example application of this is
`IsDedekindDomain.HeightOneSpectrum.adicCompletion`, which is the completion of the field of
fractions of a Dedekind domain with respect to a height-one prime ideal of the domain.

## Main definitions
- `WithVal` : type synonym for a ring equipped with the topology coming from a valuation.
- `WithVal.equiv` : the canonical ring equivalence between `WithValuation v` and `R`.
- `Valuation.Completion` : the uniform space completion of a field `K` according to the
  uniform structure defined by the specified valuation.
-/

noncomputable section

variable {R Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

structure WithVal [Ring R] (v : Valuation R Γ₀) where
  /-- Converts an element of `R` to an element of `WithVal v`. -/
  toVal (v) ::
  /-- Converts an element of `WithVal v` to an element of `R`. -/
  ofVal : R

section Notation

open Lean.PrettyPrinter.Delaborator
