/-
Extracted from CategoryTheory/Galois/Prorepresentability.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Pro-Representability of fiber functors

We show that any fiber functor is pro-representable, i.e. there exists a pro-object
`X : I ⥤ C` such that `F` is naturally isomorphic to the colimit of `X ⋙ coyoneda`.

From this we deduce the canonical isomorphism of `Aut F` with the limit over the automorphism
groups of all Galois objects.

## Main definitions

- `PointedGaloisObject`: the category of pointed Galois objects
- `PointedGaloisObject.cocone`: a cocone on `(PointedGaloisObject.incl F).op ≫ coyoneda` with
  point `F ⋙ FintypeCat.incl`.
- `autGaloisSystem`: the system of automorphism groups indexed by the pointed Galois objects.

## Main results

- `PointedGaloisObject.isColimit`: the cocone `PointedGaloisObject.cocone` is a colimit cocone.
- `autMulEquivAutGalois`: `Aut F` is canonically isomorphic to the limit over the automorphism
  groups of all Galois objects.
- `FiberFunctor.isPretransitive_of_isConnected`: The `Aut F` action on the fiber of a connected
  object is transitive.

## Implementation details

The pro-representability statement and the isomorphism of `Aut F` with the limit over the
automorphism groups of all Galois objects naturally forces `F` to take values in `FintypeCat.{u₂}`
where `u₂` is the `Hom`-universe of `C`. Since this is used to show that `Aut F` acts
transitively on `F.obj X` for connected `X`, we a priori only obtain this result for
the mentioned specialized universe setup. To obtain the result for `F` taking values in an arbitrary
`FintypeCat.{w}`, we postcompose with an equivalence `FintypeCat.{w} ≌ FintypeCat.{u₂}` and apply
the specialized result.

In the following the section `Specialized` is reserved for the setup where `F` takes values in
`FintypeCat.{u₂}` and the section `General` contains results holding for `F` taking values in
an arbitrary `FintypeCat.{w}`.

## References

* [lenstraGSchemes]: H. W. Lenstra. Galois theory for schemes.

-/

universe u₁ u₂ w

namespace CategoryTheory

namespace PreGaloisCategory

open Limits Functor

variable {C : Type u₁} [Category.{u₂} C] [GaloisCategory C]

structure PointedGaloisObject (F : C ⥤ FintypeCat.{w}) : Type (max u₁ u₂ w) where
  /-- The underlying object of `C`. -/
  obj : C
  /-- An element of the fiber of `obj`. -/
  pt : F.obj obj
  /-- `obj` is Galois. -/
  isGalois : IsGalois obj := by infer_instance

namespace PointedGaloisObject

section General

variable (F : C ⥤ FintypeCat.{w})

attribute [instance] isGalois

-- INSTANCE (free from Core): (X

variable {F} in
