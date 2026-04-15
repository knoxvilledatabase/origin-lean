/-
Extracted from MeasureTheory/Integral/TorusIntegral.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Integral over a torus in `ℂⁿ`

In this file we define the integral of a function `f : ℂⁿ → E` over a torus
`{z : ℂⁿ | ∀ i, z i ∈ Metric.sphere (c i) (R i)}`. In order to do this, we define
`torusMap (c : ℂⁿ) (R θ : ℝⁿ)` to be the point in `ℂⁿ` given by $z_k=c_k+R_ke^{θ_ki}$,
where $i$ is the imaginary unit, then define `torusIntegral f c R` as the integral over
the cube $[0, (fun _ ↦ 2π)] = \{θ\|∀ k, 0 ≤ θ_k ≤ 2π\}$ of the Jacobian of the
`torusMap` multiplied by `f (torusMap c R θ)`.

We also define a predicate saying that `f ∘ torusMap c R` is integrable on the cube
`[0, (fun _ ↦ 2π)]`.

## Main definitions

* `torusMap c R`: the generalized multidimensional exponential map from `ℝⁿ` to `ℂⁿ` that sends
  $θ=(θ_0,…,θ_{n-1})$ to $z=(z_0,…,z_{n-1})$, where $z_k= c_k + R_ke^{θ_k i}$;

* `TorusIntegrable f c R`: a function `f : ℂⁿ → E` is integrable over the generalized torus
  with center `c : ℂⁿ` and radius `R : ℝⁿ` if `f ∘ torusMap c R` is integrable on the
  closed cube `Icc (0 : ℝⁿ) (fun _ ↦ 2 * π)`;

* `torusIntegral f c R`: the integral of a function `f : ℂⁿ → E` over a torus with
  center `c ∈ ℂⁿ` and radius `R ∈ ℝⁿ` defined as
  $\iiint_{[0, 2 * π]} (∏_{k = 1}^{n} i R_k e^{θ_k * i}) • f (c + Re^{θ_k i})\,dθ_0…dθ_{k-1}$.

## Main statements

* `torusIntegral_dim0`, `torusIntegral_dim1`, `torusIntegral_succ`: formulas for `torusIntegral`
  in cases of dimension `0`, `1`, and `n + 1`.

## Notation

- `ℝ⁰`, `ℝ¹`, `ℝⁿ`, `ℝⁿ⁺¹`: local notation for `Fin 0 → ℝ`, `Fin 1 → ℝ`, `Fin n → ℝ`, and
  `Fin (n + 1) → ℝ`, respectively;
- `ℂ⁰`, `ℂ¹`, `ℂⁿ`, `ℂⁿ⁺¹`: local notation for `Fin 0 → ℂ`, `Fin 1 → ℂ`, `Fin n → ℂ`, and
  `Fin (n + 1) → ℂ`, respectively;
- `∯ z in T(c, R), f z`: notation for `torusIntegral f c R`;
- `∮ z in C(c, R), f z`: notation for `circleIntegral f c R`, defined elsewhere;
- `∏ k, f k`: notation for `Finset.prod`, defined elsewhere;
- `π`: notation for `Real.pi`, defined elsewhere.

## Tags

integral, torus
-/

variable {n : ℕ}

variable {E : Type*} [NormedAddCommGroup E]

noncomputable section

open Complex Set MeasureTheory Function Filter TopologicalSpace

open Mathlib.Tactic (superscriptTerm)

open scoped Real

local syntax:arg term:max noWs superscriptTerm : term

local macro_rules | `($t:term$n:superscript) => `(Fin $n → $t)

/-!
### `torusMap`, a parametrization of a torus
-/

def torusMap (c : ℂⁿ) (R : ℝⁿ) : ℝⁿ → ℂⁿ := fun θ i => c i + R i * exp (θ i * I)

theorem torusMap_sub_center (c : ℂⁿ) (R : ℝⁿ) (θ : ℝⁿ) : torusMap c R θ - c = torusMap 0 R θ := by
  ext1 i; simp [torusMap]

theorem torusMap_eq_center_iff {c : ℂⁿ} {R : ℝⁿ} {θ : ℝⁿ} : torusMap c R θ = c ↔ R = 0 := by
  simp [funext_iff, torusMap, exp_ne_zero]
