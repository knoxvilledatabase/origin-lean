/-
Extracted from AlgebraicGeometry/Fiber.lean
Genuine: 3 of 4 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Scheme-theoretic fiber

## Main result
- `AlgebraicGeometry.Scheme.Hom.fiber`: `f.fiber y` is the scheme-theoretic fiber of `f` at `y`.
- `AlgebraicGeometry.Scheme.Hom.fiberHomeo`: `f.fiber y` is homeomorphic to `f ⁻¹' {y}`.
- `AlgebraicGeometry.Scheme.Hom.finite_preimage`: Finite morphisms have finite fibers.
- `AlgebraicGeometry.Scheme.Hom.discrete_fiber`: Finite morphisms have discrete fibers.

-/

universe u

noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

def Scheme.Hom.fiber (f : X ⟶ Y) (y : Y) : Scheme := pullback f (Y.fromSpecResidueField y)

def Scheme.Hom.fiberι (f : X ⟶ Y) (y : Y) : f.fiber y ⟶ X := pullback.fst _ _

-- INSTANCE (free from Core): (f

def Scheme.Hom.fiberToSpecResidueField (f : X ⟶ Y) (y : Y) :
    f.fiber y ⟶ Spec (Y.residueField y) :=
  pullback.snd _ _
