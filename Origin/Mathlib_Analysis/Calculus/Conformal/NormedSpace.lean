/-
Extracted from Analysis/Calculus/Conformal/NormedSpace.lean
Genuine: 2 of 3 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core

/-!
# Conformal Maps

A continuous linear map between real normed spaces `X` and `Y` is `ConformalAt` some point `x`
if it is real differentiable at that point and its differential is a conformal linear map.

## Main definitions

* `ConformalAt`: the main definition of conformal maps
* `Conformal`: maps that are conformal at every point

## Main results
* The conformality of the composition of two conformal maps, the identity map
  and multiplications by nonzero constants
* `conformalAt_iff_isConformalMap_fderiv`: an equivalent definition of the conformality of a map

In `Analysis.Calculus.Conformal.InnerProduct`:
* `conformalAt_iff`: an equivalent definition of the conformality of a map

In `Geometry.Euclidean.Angle.Unoriented.Conformal`:
* `ConformalAt.preserves_angle`: if a map is conformal at `x`, then its differential preserves
  all angles at `x`

## Tags

conformal

## Warning

The definition of conformality in this file does NOT require the maps to be orientation-preserving.
Maps such as the complex conjugate are considered to be conformal.
-/

noncomputable section

variable {X Y Z : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedAddCommGroup Z]
  [NormedSpace ℝ X] [NormedSpace ℝ Y] [NormedSpace ℝ Z]

section LocConformality

open LinearIsometry ContinuousLinearMap

def ConformalAt (f : X → Y) (x : X) :=
  ∃ f' : X →L[ℝ] Y, HasFDerivAt f f' x ∧ IsConformalMap f'

theorem conformalAt_id (x : X) : ConformalAt _root_.id x :=
  ⟨.id ℝ X, hasFDerivAt_id _, isConformalMap_id⟩

-- DISSOLVED: conformalAt_const_smul
