/-
Extracted from Geometry/RingedSpace/LocallyRingedSpace/ResidueField.lean
Genuine: 3 of 4 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!

# Residue fields of points

Any point `x` of a locally ringed space `X` comes with a natural residue field, namely the residue
field of the stalk at `x`. Moreover, for every open subset of `X` containing `x`, we have a
canonical evaluation map from `Γ(X, U)` to the residue field of `X` at `x`.

## Main definitions

The following are in the `AlgebraicGeometry.LocallyRingedSpace` namespace:

- `residueField`: the residue field of the stalk at `x`.
- `evaluation`: for open subsets `U` of `X` containing `x`, the evaluation map from sections over
  `U` to the residue field at `x`.
- `evaluationMap`: a morphism of locally ringed spaces induces a morphism, i.e. extension, of
  residue fields.

-/

universe u

open CategoryTheory TopologicalSpace Opposite

noncomputable section

namespace AlgebraicGeometry.LocallyRingedSpace

variable (X : LocallyRingedSpace.{u}) {U : Opens X}

def residueField (x : X) : CommRingCat :=
  CommRingCat.of <| IsLocalRing.ResidueField (X.presheaf.stalk x)

-- INSTANCE (free from Core): (x

def evaluation (x : U) : X.presheaf.obj (op U) ⟶ X.residueField x :=
  -- TODO: make a new definition wrapping
  -- `CommRingCat.ofHom (IsLocalRing.residue (X.presheaf.stalk _))`?
  X.presheaf.germ U x.1 x.2 ≫ CommRingCat.ofHom (IsLocalRing.residue (X.presheaf.stalk _))

def Γevaluation (x : X) : X.presheaf.obj (op ⊤) ⟶ X.residueField x :=
  X.evaluation ⟨x, show x ∈ ⊤ from trivial⟩

set_option backward.isDefEq.respectTransparency false in
