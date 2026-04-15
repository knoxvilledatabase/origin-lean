/-
Extracted from Data/DFinsupp/BigOperators.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Dependent functions with finite support

For a non-dependent version see `Mathlib/Data/Finsupp/Defs.lean`.

## Notation

This file introduces the notation `Π₀ a, β a` as notation for `DFinsupp β`, mirroring the `α →₀ β`
notation used for `Finsupp`. This works for nested binders too, with `Π₀ a b, γ a b` as notation
for `DFinsupp (fun a ↦ DFinsupp (γ a))`.

## Implementation notes

The support is internally represented (in the primed `DFinsupp.support'`) as a `Multiset` that
represents a superset of the true support of the function, quotiented by the always-true relation so
that this does not impact equality. This approach has computational benefits over storing a
`Finset`; it allows us to add together two finitely-supported functions without
having to evaluate the resulting function to recompute its support (which would required
decidability of `b = 0` for `b : β i`).

The true support of the function can still be recovered with `DFinsupp.support`; but these
decidability obligations are now postponed to when the support is actually needed. As a consequence,
there are two ways to sum a `DFinsupp`: with `DFinsupp.sum` which works over an arbitrary function
but requires recomputation of the support and therefore a `Decidable` argument; and with
`DFinsupp.sumAddHom` which requires an additive morphism, using its properties to show that
summing over a superset of the support is sufficient.

`Finsupp` takes an altogether different approach here; it uses `Classical.Decidable` and declares
the `Add` instance as noncomputable. This design difference is independent of the fact that
`DFinsupp` is dependently-typed and `Finsupp` is not; in future, we may want to align these two
definitions, or introduce two more definitions for the other combinations of decisions.
-/

universe u u₁ u₂ v v₁ v₂ v₃ w x y l

variable {ι : Type u} {γ : Type w} {β : ι → Type v} {β₁ : ι → Type v₁} {β₂ : ι → Type v₂}

namespace DFinsupp

section Algebra

def evalAddMonoidHom [∀ i, AddZeroClass (β i)] (i : ι) : (Π₀ i, β i) →+ β i :=
  (Pi.evalAddMonoidHom β i).comp coeFnAddMonoidHom
