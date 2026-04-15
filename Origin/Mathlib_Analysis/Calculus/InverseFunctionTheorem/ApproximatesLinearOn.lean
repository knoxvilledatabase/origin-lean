/-
Extracted from Analysis/Calculus/InverseFunctionTheorem/ApproximatesLinearOn.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Non-linear maps close to affine maps

In this file we study a map `f` such that `‖f x - f y - f' (x - y)‖ ≤ c * ‖x - y‖` on an open set
`s`, where `f' : E →L[𝕜] F` is a continuous linear map and `c` is suitably small. Maps of this type
behave like `f a + f' (x - a)` near each `a ∈ s`.

When `f'` is onto, we show that `f` is locally onto.

When `f'` is a continuous linear equiv, we show that `f` is a homeomorphism
between `s` and `f '' s`. More precisely, we define `ApproximatesLinearOn.toOpenPartialHomeomorph`
to be an `OpenPartialHomeomorph` with `toFun = f`, `source = s`, and `target = f '' s`.
between `s` and `f '' s`. More precisely, we define `ApproximatesLinearOn.toOpenPartialHomeomorph`
to be an `OpenPartialHomeomorph` with `toFun = f`, `source = s`, and `target = f '' s`.

Maps of this type naturally appear in the proof of the inverse function theorem (see next section),
and `ApproximatesLinearOn.toOpenPartialHomeomorph` will imply that the locally inverse function
and `ApproximatesLinearOn.toOpenPartialHomeomorph` will imply that the locally inverse function
exists.

We define this auxiliary notion to split the proof of the inverse function theorem into small
lemmas. This approach makes it possible

- to prove a lower estimate on the size of the domain of the inverse function;

- to reuse parts of the proofs in the case if a function is not strictly differentiable. E.g., for a
  function `f : E × F → G` with estimates on `f x y₁ - f x y₂` but not on `f x₁ y - f x₂ y`.

## Notation

We introduce some `local notation` to make formulas shorter:

* by `N` we denote `‖f'⁻¹‖`;
* by `g` we denote the auxiliary contracting map `x ↦ x + f'.symm (y - f x)` used to prove that
  `{x | f x = y}` is nonempty.
-/

open Function Set Filter Metric

open scoped Topology NNReal

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable {ε : ℝ}

open Filter Metric Set

open ContinuousLinearMap (id)

def ApproximatesLinearOn (f : E → F) (f' : E →L[𝕜] F) (s : Set E) (c : ℝ≥0) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, ‖f x - f y - f' (x - y)‖ ≤ c * ‖x - y‖
