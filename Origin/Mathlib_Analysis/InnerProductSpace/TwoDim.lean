/-
Extracted from Analysis/InnerProductSpace/TwoDim.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Oriented two-dimensional real inner product spaces

This file defines constructions specific to the geometry of an oriented two-dimensional real inner
product space `E`.

## Main declarations

* `Orientation.areaForm`: an antisymmetric bilinear form `E →ₗ[ℝ] E →ₗ[ℝ] ℝ` (usual notation `ω`).
  Morally, when `ω` is evaluated on two vectors, it gives the oriented area of the parallelogram
  they span. (But mathlib does not yet have a construction of oriented area, and in fact the
  construction of oriented area should pass through `ω`.)

* `Orientation.rightAngleRotation`: an isometric automorphism `E ≃ₗᵢ[ℝ] E` (usual notation `J`).
  This automorphism squares to -1. In a later file, rotations (`Orientation.rotation`) are defined,
  in such a way that this automorphism is equal to rotation by 90 degrees.

* `Orientation.basisRightAngleRotation`: for a nonzero vector `x` in `E`, the basis `![x, J x]`
  for `E`.

* `Orientation.kahler`: a complex-valued real-bilinear map `E →ₗ[ℝ] E →ₗ[ℝ] ℂ`. Its real part is the
  inner product and its imaginary part is `Orientation.areaForm`. For vectors `x` and `y` in `E`,
  the complex number `o.kahler x y` has modulus `‖x‖ * ‖y‖`. In a later file, oriented angles
  (`Orientation.oangle`) are defined, in such a way that the argument of `o.kahler x y` is the
  oriented angle from `x` to `y`.

## Main results

* `Orientation.rightAngleRotation_rightAngleRotation`: the identity `J (J x) = - x`

* `Orientation.nonneg_inner_and_areaForm_eq_zero_iff_sameRay`: `x`, `y` are in the same ray, if
  and only if `0 ≤ ⟪x, y⟫` and `ω x y = 0`

* `Orientation.kahler_mul`: the identity `o.kahler x a * o.kahler a y = ‖a‖ ^ 2 * o.kahler x y`

* `Complex.areaForm`, `Complex.rightAngleRotation`, `Complex.kahler`: the concrete
  interpretations of `areaForm`, `rightAngleRotation`, `kahler` for the oriented real inner
  product space `ℂ`

* `Orientation.areaForm_map_complex`, `Orientation.rightAngleRotation_map_complex`,
  `Orientation.kahler_map_complex`: given an orientation-preserving isometry from `E` to `ℂ`,
  expressions for `areaForm`, `rightAngleRotation`, `kahler` as the pullback of their concrete
  interpretations on `ℂ`

## Implementation notes

Notation `ω` for `Orientation.areaForm` and `J` for `Orientation.rightAngleRotation` should be
defined locally in each file which uses them, since otherwise one would need a more cumbersome
notation which mentions the orientation explicitly (something like `ω[o]`). Write

```
local notation "ω" => o.areaForm
local notation "J" => o.rightAngleRotation
```

-/

noncomputable section

open scoped RealInnerProductSpace ComplexConjugate

open Module

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fact (finrank ℝ E = 2)]
  (o : Orientation ℝ E (Fin 2))

namespace Orientation

irreducible_def areaForm : E →ₗ[ℝ] E →ₗ[ℝ] ℝ := by
  let z : E [⋀^Fin 0]→ₗ[ℝ] ℝ ≃ₗ[ℝ] ℝ :=
    AlternatingMap.constLinearEquivOfIsEmpty.symm
  let y : E [⋀^Fin 1]→ₗ[ℝ] ℝ →ₗ[ℝ] E →ₗ[ℝ] ℝ :=
    LinearMap.llcomp ℝ E (E [⋀^Fin 0]→ₗ[ℝ] ℝ) ℝ z ∘ₗ AlternatingMap.curryLeftLinearMap
  exact y ∘ₗ AlternatingMap.curryLeftLinearMap o.volumeForm

local notation "ω" => o.areaForm

theorem areaForm_to_volumeForm (x y : E) : ω x y = o.volumeForm ![x, y] := by simp [areaForm]
