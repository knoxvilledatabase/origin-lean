/-
Extracted from Analysis/CStarAlgebra/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Normed star rings and algebras

A normed star group is a normed group with a compatible `star` which is isometric.

A C⋆-ring is a normed star group that is also a ring and that verifies the stronger
condition `‖x‖^2 ≤ ‖x⋆ * x‖` for all `x` (which actually implies equality). If a C⋆-ring is also
a star algebra, then it is a C⋆-algebra.

Note that the type classes corresponding to C⋆-algebras are defined in
`Mathlib/Analysis/CStarAlgebra/Classes`.

## TODO

- Show that `‖x⋆ * x‖ = ‖x‖^2` is equivalent to `‖x⋆ * x‖ = ‖x⋆‖ * ‖x‖`, which is used as the
  definition of C*-algebras in some sources (e.g. Wikipedia).

-/

assert_not_exists ContinuousLinearMap.hasOpNorm

open Topology

local postfix:max "⋆" => star

class NormedStarGroup (E : Type*) [SeminormedAddCommGroup E] [StarAddMonoid E] : Prop where
  norm_star_le : ∀ x : E, ‖x⋆‖ ≤ ‖x‖

variable {𝕜 E α : Type*}

section NormedStarGroup

variable [SeminormedAddCommGroup E] [StarAddMonoid E] [NormedStarGroup E]
