/-
Extracted from Topology/Sheaves/PresheafOfFunctions.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Presheaves of functions

We construct some simple examples of presheaves of functions on a topological space.
* `presheafToTypes X T`, where `T : X → Type`,
  is the presheaf of dependently-typed (not-necessarily continuous) functions
* `presheafToType X T`, where `T : Type`,
  is the presheaf of (not-necessarily-continuous) functions to a fixed target type `T`
* `presheafToTop X T`, where `T : TopCat`,
  is the presheaf of continuous functions into a topological space `T`
* `presheafToTopCommRing X R`, where `R : TopCommRingCat`
  is the presheaf valued in `CommRing` of functions into a topological ring `R`
* as an example of the previous construction,
  `presheafToTopCommRing X (TopCommRingCat.of ℂ)`
  is the presheaf of rings of continuous complex-valued functions on `X`.
-/

open CategoryTheory TopologicalSpace Opposite

namespace TopCat

variable (X : TopCat)

def presheafToTypes (T : X → Type*) : X.Presheaf (Type _) where
  obj U := ∀ x : U.unop, T x
  map {_ V} i := TypeCat.ofHom (fun (g) (x : V.unop) => g (i.unop x))
