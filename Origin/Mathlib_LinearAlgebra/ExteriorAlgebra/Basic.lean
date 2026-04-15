/-
Extracted from LinearAlgebra/ExteriorAlgebra/Basic.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Exterior Algebras

We construct the exterior algebra of a module `M` over a commutative semiring `R`.

## Notation

The exterior algebra of the `R`-module `M` is denoted as `ExteriorAlgebra R M`.
It is endowed with the structure of an `R`-algebra.

The `n`th exterior power of the `R`-module `M` is denoted by `exteriorPower R n M`;
it is of type `Submodule R (ExteriorAlgebra R M)` and defined as
`LinearMap.range (ExteriorAlgebra.ι R : M →ₗ[R] ExteriorAlgebra R M) ^ n`.
We also introduce the notation `⋀[R]^n M` for `exteriorPower R n M`.

Given a linear morphism `f : M → A` from a module `M` to another `R`-algebra `A`, such that
`cond : ∀ m : M, f m * f m = 0`, there is a (unique) lift of `f` to an `R`-algebra morphism,
which is denoted `ExteriorAlgebra.lift R f cond`.

The canonical linear map `M → ExteriorAlgebra R M` is denoted `ExteriorAlgebra.ι R`.

## Theorems

The main theorems proved ensure that `ExteriorAlgebra R M` satisfies the universal property
of the exterior algebra.
1. `ι_comp_lift` is the fact that the composition of `ι R` with `lift R f cond` agrees with `f`.
2. `lift_unique` ensures the uniqueness of `lift R f cond` with respect to 1.

## Definitions

* `ιMulti` is the `AlternatingMap` corresponding to the wedge product of `ι R m` terms.

## Implementation details

The exterior algebra of `M` is constructed as simply `CliffordAlgebra (0 : QuadraticForm R M)`,
as this avoids us having to duplicate API.
-/

universe u1 u2 u3 u4 u5

variable (R : Type u1) [CommRing R]

variable (M : Type u2) [AddCommGroup M] [Module R M]

abbrev ExteriorAlgebra :=
  CliffordAlgebra (0 : QuadraticForm R M)

namespace ExteriorAlgebra

variable {M}

abbrev ι : M →ₗ[R] ExteriorAlgebra R M :=
  CliffordAlgebra.ι _

section exteriorPower

variable (n : ℕ) (M : Type u2) [AddCommGroup M] [Module R M]

abbrev exteriorPower : Submodule R (ExteriorAlgebra R M) :=
  LinearMap.range (ι R : M →ₗ[R] ExteriorAlgebra R M) ^ n
