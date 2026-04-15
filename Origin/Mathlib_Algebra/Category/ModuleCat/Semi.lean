/-
Extracted from Algebra/Category/ModuleCat/Semi.lean
Genuine: 2 of 4 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# The category of `R`-modules

If `R` is a semiring, `SemimoduleCat.{v} R` is the category of bundled `R`-semimodules with carrier
in the universe `v`. We show that it is preadditive and show that being an isomorphism and
monomorphism are equivalent to being a linear equivalence and an injective linear map respectively.

## Implementation details

To construct an object in the category of `R`-semimodules from a type `M` with an instance of the
`Module` typeclass, write `of R M`. There is a coercion in the other direction.
The roundtrip `↑(of R M)` is definitionally equal to `M` itself (when `M` is a type with `Module`
instance), and so is `of R ↑M` (when `M : SemimoduleCat R M`).

The morphisms are given their own type, not identified with `LinearMap`.
There is a cast from morphisms in `Module R` to linear maps,
written `f.hom` (`SemimoduleCat.Hom.hom`).
To go from linear maps to morphisms in `Module R`, use `SemimoduleCat.ofHom`.

Similarly, given an isomorphism `f : M ≅ N` use `f.toLinearEquiv` and given a linear equiv
`f : M ≃ₗ[R] N`, use `f.toModuleIso`.
-/

open CategoryTheory Limits WalkingParallelPair

universe v u

variable (R : Type u) [Semiring R]

set_option backward.privateInPublic true in

structure SemimoduleCat where
  private mk ::
  /-- the underlying type of an object in `SemimoduleCat R` -/
  carrier : Type v
  [isAddCommMonoid : AddCommMonoid carrier]
  [isModule : Module R carrier]

attribute [instance] SemimoduleCat.isAddCommMonoid SemimoduleCat.isModule

namespace SemimoduleCat

-- INSTANCE (free from Core): :

attribute [coe] SemimoduleCat.carrier

set_option backward.privateInPublic true in

set_option backward.privateInPublic.warn false in

abbrev of (X : Type v) [AddCommMonoid X] [Module R X] : SemimoduleCat.{v} R :=
  ⟨X⟩

example (X : Type v) [Semiring X] [Module R X] : (of R X : Type v) = X := by with_reducible rfl

example (M : SemimoduleCat.{v} R) : of R M = M := by with_reducible rfl

variable {R} in
