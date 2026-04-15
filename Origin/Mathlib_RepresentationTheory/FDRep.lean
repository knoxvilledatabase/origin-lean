/-
Extracted from RepresentationTheory/FDRep.lean
Genuine: 2 of 4 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# `FDRep k G` is the category of finite-dimensional `k`-linear representations of `G`.

If `V : FDRep k G`, there is a coercion that allows you to treat `V` as a type,
and this type comes equipped with `Module k V` and `FiniteDimensional k V` instances.
Also `V.ρ` gives the homomorphism `G →* (V →ₗ[k] V)`.

Conversely, given a homomorphism `ρ : G →* (V →ₗ[k] V)`,
you can construct the bundled representation as `Rep.of ρ`.

We prove Schur's Lemma: the dimension of the `Hom`-space between two irreducible representation is
`0` if they are not isomorphic, and `1` if they are.
This is the content of `finrank_hom_simple_simple`

We verify that `FDRep k G` is a `k`-linear monoidal category, and rigid when `G` is a group.

`FDRep k G` has all finite limits.

## Implementation notes

We define `FDRep R G` for any ring `R` and monoid `G`,
as the category of finitely generated `R`-linear representations of `G`.

The main case of interest is when `R = k` is a field and `G` is a group,
and this is reflected in the documentation.

## TODO
* `FdRep k G ≌ FullSubcategory (FiniteDimensional k)`
* `FdRep k G` has all finite colimits.
* `FdRep k G` is abelian.
* `FdRep k G ≌ FGModuleCat k[G]`.

-/

suppress_compilation

universe u

open CategoryTheory

open CategoryTheory.Limits

abbrev FDRep (R G : Type u) [Ring R] [Monoid G] :=
  Action (FGModuleCat.{u} R) G

namespace FDRep

variable {R k G : Type u} [CommRing R] [Field k] [Monoid G]

example : LargeCategory (FDRep R G) := by infer_instance

example : ConcreteCategory (FDRep R G) (Action.HomSubtype _ _) := by infer_instance

example : Preadditive (FDRep R G) := by infer_instance

example : HasFiniteLimits (FDRep k G) := by infer_instance

example : Linear R (FDRep R G) := by infer_instance

-- INSTANCE (free from Core): :

example (V : FDRep R G) : Module.Finite R V := by infer_instance

-- INSTANCE (free from Core): (V

def ρ (V : FDRep R G) : G →* V →ₗ[R] V :=
  (ModuleCat.endRingEquiv _).toMonoidHom.comp
    (InducedCategory.endEquiv.toMonoidHom.comp (Action.ρ V))
