/-
Extracted from Algebra/Category/ModuleCat/Basic.lean
Genuine: 2 of 5 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# The category of `R`-modules

`ModuleCat.{v} R` is the category of bundled `R`-modules with carrier in the universe `v`. We show
that it is preadditive and show that being an isomorphism, monomorphism and epimorphism is
equivalent to being a linear equivalence, an injective linear map and a surjective linear map,
respectively.

## Implementation details

To construct an object in the category of `R`-modules from a type `M` with an instance of the
`Module` typeclass, write `of R M`. There is a coercion in the other direction.
The roundtrip `↑(of R M)` is definitionally equal to `M` itself (when `M` is a type with `Module`
instance), and so is `of R ↑M` (when `M : ModuleCat R M`).

The morphisms are given their own type, not identified with `LinearMap`.
There is a cast from morphisms in `Module R` to linear maps, written `f.hom` (`ModuleCat.Hom.hom`).
To go from linear maps to morphisms in `Module R`, use `ModuleCat.ofHom`.

Similarly, given an isomorphism `f : M ≅ N` use `f.toLinearEquiv` and given a linear equiv
`f : M ≃ₗ[R] N`, use `f.toModuleIso`.
-/

open CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.Limits.WalkingParallelPair

universe v u

variable (R : Type u) [Ring R]

set_option backward.privateInPublic true in

structure ModuleCat where
  private mk ::
  /-- the underlying type of an object in `ModuleCat R` -/
  carrier : Type v
  [isAddCommGroup : AddCommGroup carrier]
  [isModule : Module R carrier]

attribute [instance] ModuleCat.isAddCommGroup

-- INSTANCE (free from Core): 1100]

namespace ModuleCat

-- INSTANCE (free from Core): :

attribute [coe] ModuleCat.carrier

set_option backward.privateInPublic true in

set_option backward.privateInPublic.warn false in

abbrev of (X : Type v) [AddCommGroup X] [Module R X] : ModuleCat.{v} R :=
  ⟨X⟩

example (X : Type v) [Ring X] [Module R X] : (of R X : Type v) = X := by with_reducible rfl

example (M : ModuleCat.{v} R) : of R M = M := by with_reducible rfl

set_option backward.privateInPublic true in

variable {R} in
