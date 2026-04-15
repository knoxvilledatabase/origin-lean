/-
Extracted from AlgebraicGeometry/Morphisms/AffineAnd.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Affine morphisms with additional ring hom property

In this file we define a constructor `affineAnd Q` for affine target morphism properties of schemes
from a property of ring homomorphisms `Q`: A morphism `f : X ⟶ Y` with affine target satisfies
`affineAnd Q` if it is an affine morphism (i.e. `X` is affine) and the induced ring map on global
sections satisfies `Q`.

`affineAnd Q` inherits most stability properties of `Q` and is local at the target if `Q` is local
at the (algebraic) source.

Typical examples of this are affine morphisms (where `Q` is trivial), finite morphisms
(where `Q` is module finite) or closed immersions (where `Q` is being surjective).

-/

universe v u

open CategoryTheory TopologicalSpace Opposite MorphismProperty

namespace AlgebraicGeometry

variable (Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop)

def affineAnd : AffineTargetMorphismProperty :=
  fun X _ f ↦ IsAffine X ∧ Q (f.appTop).hom
