/-
Extracted from AlgebraicGeometry/AffineScheme.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Affine schemes

We define the category of `AffineScheme`s as the essential image of `Spec`.
We also define predicates about affine schemes and affine open sets.

## Main definitions

* `AlgebraicGeometry.AffineScheme`: The category of affine schemes.
* `AlgebraicGeometry.IsAffine`: A scheme is affine if the canonical map `X ⟶ Spec Γ(X)` is an
  isomorphism.
* `AlgebraicGeometry.Scheme.isoSpec`: The canonical isomorphism `X ≅ Spec Γ(X)` for an affine
  scheme.
* `AlgebraicGeometry.AffineScheme.equivCommRingCat`: The equivalence of categories
  `AffineScheme ≌ CommRingᵒᵖ` given by `AffineScheme.Spec : CommRingᵒᵖ ⥤ AffineScheme` and
  `AffineScheme.Γ : AffineSchemeᵒᵖ ⥤ CommRingCat`.
* `AlgebraicGeometry.IsAffineOpen`: An open subset of a scheme is affine if the open subscheme is
  affine.
* `AlgebraicGeometry.IsAffineOpen.fromSpec`: The immersion `Spec 𝒪ₓ(U) ⟶ X` for an affine `U`.

-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

open Spec (structureSheaf)

def AffineScheme :=
  Scheme.Spec.EssImageSubcategory

deriving Category

class IsAffine (X : Scheme) : Prop where
  affine : IsIso X.toSpecΓ

attribute [instance] IsAffine.affine

-- INSTANCE (free from Core): (X
