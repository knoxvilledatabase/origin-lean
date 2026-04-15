/-
Extracted from Topology/Path.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Paths in topological spaces

This file introduces continuous paths and provides API for them.

## Main definitions

In this file the unit interval `[0, 1]` in `ℝ` is denoted by `I`, and `X` is a topological space.

* `Path x y` is the type of paths from `x` to `y`, i.e., continuous maps from `I` to `X`
  mapping `0` to `x` and `1` to `y`.
* `Path.refl x : Path x x` is the constant path at `x`.
* `Path.symm γ : Path y x` is the reverse of a path `γ : Path x y`.
* `Path.trans γ γ' : Path x z` is the concatenation of two paths `γ : Path x y`, `γ' : Path y z`.
* `Path.map γ hf : Path (f x) (f y)` is the image of `γ : Path x y` under a continuous map `f`.
* `Path.reparam γ f hf hf₀ hf₁ : Path x y` is the reparametrisation of `γ : Path x y` by
  a continuous map `f : I → I` fixing `0` and `1`.
* `Path.truncate γ t₀ t₁ : Path (γ t₀) (γ t₁)` is the path that follows `γ` from `t₀` to `t₁` and
  stays constant otherwise.
* `Path.extend γ : C(ℝ, X)` is the extension `γ` to `ℝ` that is constant before `0` and after `1`.

`Path x y` is equipped with the topology induced by the compact-open topology on `C(I,X)`, and
several of the above constructions are shown to be continuous.

## Implementation notes

By default, all paths have `I` as their source and `X` as their target, but there is an
operation `Set.IccExtend` that will extend any continuous map `γ : I → X` into a continuous map
`IccExtend zero_le_one γ : ℝ → X` that is constant before `0` and after `1`.

This is used to define `Path.extend` that turns `γ : Path x y` into a continuous map
`γ.extend : ℝ → X` whose restriction to `I` is the original `γ`, and is equal to `x`
on `(-∞, 0]` and to `y` on `[1, +∞)`.
-/

noncomputable section

open Topology Filter unitInterval Set Function

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x y z : X} {ι : Type*}

/-! ### Paths -/

structure Path (x y : X) extends C(I, X) where
  /-- The start point of a `Path`. -/
  source' : toFun 0 = x
  /-- The end point of a `Path`. -/
  target' : toFun 1 = y

-- INSTANCE (free from Core): Path.instFunLike

-- INSTANCE (free from Core): Path.continuousMapClass
