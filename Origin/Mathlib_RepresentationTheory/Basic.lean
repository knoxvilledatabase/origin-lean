/-
Extracted from RepresentationTheory/Basic.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Monoid representations

This file introduces monoid representations and their characters and defines a few ways to construct
representations.

## Main definitions

  * `Representation`
  * `Representation.directSum`
  * `Representation.prod`
  * `Representation.tprod`
  * `Representation.linHom`
  * `Representation.dual`
  * `Representation.free`

## Implementation notes

Representations of a monoid `G` on a `k`-module `V` are implemented as
homomorphisms `G →* (V →ₗ[k] V)`. We use the abbreviation `Representation` for this hom space.

The theorem `asAlgebraHom_def` constructs a module over the group `k`-algebra of `G` (implemented
as `k[G]`) corresponding to a representation. If `ρ : Representation k G V`, this
module can be accessed via `ρ.asModule`. Conversely, given a `k[G]`-module `M`,
`M.ofModule` is the associated representation seen as a homomorphism.
-/

open MonoidAlgebra (lift of)

open LinearMap Module

open scoped MonoidAlgebra

variable (k G V : Type*) [Semiring k] [Monoid G] [AddCommMonoid V] [Module k V]

abbrev Representation :=
  G →* V →ₗ[k] V

end

namespace Representation

section trivial

variable (k G V : Type*) [Semiring k] [Monoid G] [AddCommMonoid V] [Module k V]

def trivial : Representation k G V :=
  1

variable {G V}
