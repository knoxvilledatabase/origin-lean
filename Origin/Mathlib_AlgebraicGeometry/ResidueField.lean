/-
Extracted from AlgebraicGeometry/ResidueField.lean
Genuine: 2 of 5 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!

# Residue fields of points

## Main definitions

The following are in the `AlgebraicGeometry.Scheme` namespace:

- `AlgebraicGeometry.Scheme.residueField`: The residue field of the stalk at `x`.
- `AlgebraicGeometry.Scheme.evaluation`: For open subsets `U` of `X` containing `x`,
  the evaluation map from sections over `U` to the residue field at `x`.
- `AlgebraicGeometry.Scheme.Hom.residueFieldMap`: A morphism of schemes induce a homomorphism of
  residue fields.
- `AlgebraicGeometry.Scheme.fromSpecResidueField`: The canonical map `Spec κ(x) ⟶ X`.
- `AlgebraicGeometry.Scheme.SpecToEquivOfField`: morphisms `Spec K ⟶ X` for a field `K` correspond
  to pairs of `x : X` with embedding `κ(x) ⟶ K`.


-/

universe u

open CategoryTheory TopologicalSpace Opposite IsLocalRing

noncomputable section

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) {U : X.Opens}

def residueField (x : X) : CommRingCat :=
  CommRingCat.of <| IsLocalRing.ResidueField (X.presheaf.stalk x)

-- INSTANCE (free from Core): (x

-- INSTANCE (free from Core): (x

def residue (X : Scheme.{u}) (x) : X.presheaf.stalk x ⟶ X.residueField x :=
  CommRingCat.ofHom (IsLocalRing.residue (X.presheaf.stalk x))

-- INSTANCE (free from Core): {X
