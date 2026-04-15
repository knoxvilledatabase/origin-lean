/-
Extracted from MeasureTheory/Integral/CurveIntegral/Basic.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Integral of a 1-form along a path

In this file we define the integral of a 1-form along a path indexed by `[0, 1]`
and prove basic properties of this operation.

The integral `∫ᶜ x in γ, ω x` is defined as $\int_0^1 \omega(\gamma(t))(\gamma'(t))$.
More precisely, we use

- `Path.extend γ t` instead of `γ t`, because both derivatives and `intervalIntegral`
  expect globally defined functions;
- `derivWithin γ.extend (Set.Icc 0 1) t`, not `deriv γ.extend t`, for the derivative,
  so that it takes meaningful values at `t = 0` and `t = 1`,
  even though this does not affect the integral.

The argument `ω : E → E →L[𝕜] F` is a `𝕜`-linear 1-form on `E` taking values in `F`,
where `𝕜` is `ℝ` or `ℂ`.
The definition does not depend on `𝕜`, see `curveIntegral_restrictScalars` and nearby lemmas.
However, the fact that `𝕜 = ℝ` is not hardcoded
allows us to avoid inserting `ContinuousLinearMap.restrictScalars` here and there.

## Main definitions

- `curveIntegral ω γ`, notation `∫ᶜ x in γ, ω x`, is the integral of a 1-form `ω` along a path `γ`.
- `CurveIntegrable ω γ` is the predicate saying that the above integral makes sense.

## Main results

We prove that `curveIntegral` behaves well with respect to

- operations on `Path`s, see `curveIntegral_refl`, `curveIntegral_symm`, `curveIntegral_trans` etc;
- algebraic operations on 1-forms, see `curveIntegral_add` etc.

We also show that the derivative of `fun b ↦ ∫ᶜ x in Path.segment a b, ω x`
has derivative `ω a` at `b = a`.
We provide 2 versions of this result: one for derivative (`HasFDerivWithinAt`) within a convex set
and one for `HasFDerivAt`.

## Implementation notes

### Naming

In literature, the integral of a function or a 1-form along a path
is called “line integral”, “path integral”, “curve integral”, or “curvilinear integral”.

We use the name “curve integral” instead of other names for the following reasons:

- for many people whose mother tongue is not English,
  “line integral” sounds like an integral along a straight line;

- we reserve the name "path integral" for Feynman-style integrals over the space of paths.

### Usage of `ContinuousLinearMap`s for 1-forms

Similarly to the way `fderiv` uses continuous linear maps
while higher order derivatives use continuous multilinear maps,
this file uses `E → E →L[𝕜] F` instead of continuous alternating maps for 1-forms.

### Differentiability assumptions

The definitions in this file make sense if the path is a piecewise $C^1$ curve.
Poincaré lemma (formalization WIP, see #24019) implies that for a closed 1-form on an open set `U`,
the integral depends on the homotopy class of the path only,
thus we can define the integral along a continuous path
or an element of the fundamental groupoid of `U`.

### Usage of an extra field

The definitions in this file deal with `𝕜`-linear 1-forms.
This allows us to avoid using `ContinuousLinearMap.restrictScalars`
in `HasFDerivWithinAt.curveIntegral_segment_source`
and a future formalization of Poincaré lemma.
-/

open Metric MeasureTheory Topology Set Interval AffineMap Convex Filter

open scoped Pointwise unitInterval

section Defs

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {a b : E}

noncomputable irreducible_def curveIntegralFun (lemma := curveIntegralFun_def')
    (ω : E → E →L[𝕜] F) (γ : Path a b) (t : ℝ) : F :=
  letI : NormedSpace ℝ E := .restrictScalars ℝ 𝕜 E
  ω (γ.extend t) (derivWithin γ.extend I t)

def CurveIntegrable (ω : E → E →L[𝕜] F) (γ : Path a b) : Prop :=
  IntervalIntegrable (curveIntegralFun ω γ) volume 0 1

noncomputable irreducible_def curveIntegral (lemma := curveIntegral_def')
    (ω : E → E →L[𝕜] F) (γ : Path a b) : F :=
  letI : NormedSpace ℝ F := .restrictScalars ℝ 𝕜 F
  ∫ t in 0..1, curveIntegralFun ω γ t
