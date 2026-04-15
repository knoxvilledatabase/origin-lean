/-
Extracted from Analysis/Normed/Operator/ContinuousLinearMap.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Constructions of continuous linear maps between (semi-)normed spaces

A fundamental fact about (semi-)linear maps between normed spaces over sensible fields is that
continuity and boundedness are equivalent conditions.  That is, for normed spaces `E`, `F`, a
`LinearMap` `f : E →ₛₗ[σ] F` is the coercion of some `ContinuousLinearMap` `f' : E →SL[σ] F`, if
and only if there exists a bound `C` such that for all `x`, `‖f x‖ ≤ C * ‖x‖`.

We prove one direction in this file: `LinearMap.mkContinuous`, boundedness implies continuity. The
other direction, `ContinuousLinearMap.bound`, is deferred to a later file, where the
strong operator topology on `E →SL[σ] F` is available, because it is natural to use
`ContinuousLinearMap.bound` to define a norm `⨆ x, ‖f x‖ / ‖x‖` on `E →SL[σ] F` and to show that
this is compatible with the strong operator topology.

This file also contains several corollaries of `LinearMap.mkContinuous`: other "easy"
constructions of continuous linear maps between normed spaces.

This file is meant to be lightweight (it is imported by much of the analysis library); think twice
before adding imports!
-/

open Metric ContinuousLinearMap

open Set Real

open NNReal

variable {𝕜 𝕜₂ E F G : Type*}

/-! ## General constructions -/

section SeminormedAddCommGroup

variable [Ring 𝕜] [Ring 𝕜₂]

variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [SeminormedAddCommGroup G]

variable [Module 𝕜 E] [Module 𝕜₂ F] [Module 𝕜 G]

variable {σ : 𝕜 →+* 𝕜₂} (f : E →ₛₗ[σ] F)

def LinearMap.mkContinuous (C : ℝ) (h : ∀ x, ‖f x‖ ≤ C * ‖x‖) : E →SL[σ] F :=
  ⟨f, AddMonoidHomClass.continuous_of_bound f C h⟩

def LinearMap.mkContinuousOfExistsBound (h : ∃ C, ∀ x, ‖f x‖ ≤ C * ‖x‖) : E →SL[σ] F :=
  ⟨f,
    let ⟨C, hC⟩ := h
    AddMonoidHomClass.continuous_of_bound f C hC⟩

theorem continuous_of_linear_of_boundₛₗ {f : E → F} (h_add : ∀ x y, f (x + y) = f x + f y)
    (h_smul : ∀ (c : 𝕜) (x), f (c • x) = σ c • f x) {C : ℝ} (h_bound : ∀ x, ‖f x‖ ≤ C * ‖x‖) :
    Continuous f :=
  let φ : E →ₛₗ[σ] F :=
    { toFun := f
      map_add' := h_add
      map_smul' := h_smul }
  AddMonoidHomClass.continuous_of_bound φ C h_bound

theorem continuous_of_linear_of_bound {f : E → G} (h_add : ∀ x y, f (x + y) = f x + f y)
    (h_smul : ∀ (c : 𝕜) (x), f (c • x) = c • f x) {C : ℝ} (h_bound : ∀ x, ‖f x‖ ≤ C * ‖x‖) :
    Continuous f :=
  let φ : E →ₗ[𝕜] G :=
    { toFun := f
      map_add' := h_add
      map_smul' := h_smul }
  AddMonoidHomClass.continuous_of_bound φ C h_bound
