/-
Extracted from AlgebraicGeometry/IdealSheaf/Functorial.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Functorial constructions of ideal sheaves

We define the pullback and pushforward of ideal sheaves in this file.

## Main definitions
- `AlgebraicGeometry.Scheme.IdealSheafData.comap`: The pullback of an ideal sheaf.
- `AlgebraicGeometry.Scheme.IdealSheafData.map`: The pushforward of an ideal sheaf.
- `AlgebraicGeometry.Scheme.IdealSheafData.map_gc`:
  The Galois connection between pullback and pushforward.

-/

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {X Y Z : Scheme.{u}}

namespace Scheme.IdealSheafData

def comap (I : Y.IdealSheafData) (f : X ⟶ Y) : X.IdealSheafData :=
  (pullback.fst f I.subschemeι).ker

def comapIso (I : Y.IdealSheafData) (f : X ⟶ Y) :
    (I.comap f).subscheme ≅ pullback f I.subschemeι :=
  (asIso (pullback.fst f I.subschemeι).toImage).symm
