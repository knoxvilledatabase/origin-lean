/-
Extracted from Analysis/Distribution/ContDiffMapSupportedIn.lean
Genuine: 5 of 8 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Continuously differentiable functions supported in a given compact set

This file develops the basic theory of bundled `n`-times continuously differentiable functions
with support contained in a given compact set.

Given `n : ℕ∞` and a compact subset `K` of a normed space `E`, we consider the type of bundled
functions `f : E → F` (where `F` is a normed vector space) such that:

- `f` is `n`-times continuously differentiable: `ContDiff ℝ n f`.
- `f` vanishes outside of a compact set: `EqOn f 0 Kᶜ`.

The main reason this exists as a bundled type is to be endowed with its natural locally convex
topology (namely, uniform convergence of `f` and its derivatives up to order `n`).
Taking the locally convex inductive limit of these as `K` varies yields the natural topology on test
functions, used to define distributions. While most of distribution theory cares only about `C^∞`
functions, we also want to endow the space of `C^n` test functions with its natural topology.
Indeed, distributions of order less than `n` are precisely those which extend continuously to this
larger space of test functions.

## Main definitions

- `ContDiffMapSupportedIn E F n K`: the type of bundled `n`-times continuously differentiable
  functions `E → F` which vanish outside of `K`.
- `ContDiffMapSupportedIn.iteratedFDerivLM`: wrapper, as a `𝕜`-linear map, for
  `iteratedFDeriv` from `ContDiffMapSupportedIn E F n K` to
  `ContDiffMapSupportedIn E (E [×i]→L[ℝ] F) k K`.
- `ContDiffMapSupportedIn.topologicalSpace`, `ContDiffMapSupportedIn.uniformSpace`: the topology
  and uniform structures on `𝓓^{n}_{K}(E, F)`, given by uniform convergence of the functions and
  all their derivatives up to order `n`.

## Main statements

- `ContDiffMapSupportedIn.isTopologicalAddGroup`, `ContDiffMapSupportedIn.continuousSMul` and
  `ContDiffMapSupportedIn.instLocallyConvexSpace`: `𝓓^{n}_{K}(E, F)` is a locally convex
  topological vector space.

## Notation

In the `Distributions` scope, we introduce the following notations:
- `𝓓^{n}_{K}(E, F)`: the space of `n`-times continuously differentiable functions `E → F`
  which vanish outside of `K`.
- `𝓓_{K}(E, F)`: the space of smooth (infinitely differentiable) functions `E → F`
  which vanish outside of `K`, i.e. `𝓓^{⊤}_{K}(E, F)`.
- `N[𝕜; F]_{K, n, i}` (or simply `N[𝕜]_{K, n, i}`): the `𝕜`-seminorm on `𝓓^{n}_{K}(E, F)`
  given by the sup-norm of the `i`-th derivative.
- `N[𝕜; F]_{K, i}` (or simply `N[𝕜]_{K, i}`): the `𝕜`-seminorm on `𝓓_{K}(E, F)`
  given by the sup-norm of the `i`-th derivative.

## Implementation details

* The technical choice of spelling `EqOn f 0 Kᶜ` in the definition, as opposed to `tsupport f ⊆ K`
  is to make rewriting `f x` to `0` easier when `x ∉ K`.
* Having the parameter `n` (instead of just using smooth functions) is useful because
  it allows us to track the regularity of our operations, which will tell us how the order
  of a distribution behaves under the transpose of said operation. For example, the fact
  that differentiation of test functions *decreases* regularity by (at most) one will imply that
  differentiation of distributions *increases* their order by (at most) one. This comes
  with the downside of many regularity parameters; we considered specializing all the
  definitions to the (most common) smooth case, but we believe it is better to wait and see
  what is more practical to use later on.
* In `iteratedFDerivLM`, we define the `i`-th iterated differentiation operator as
  a map from `𝓓^{n}_{K}` to `𝓓^{k}_{K}` without imposing relations on `n`, `k` and `i`. Of course
  this is defined as `0` if `k + i > n`. This creates some verbosity as all of these variables are
  explicit, but it allows the most flexibility while avoiding DTT hell.

## Tags

distributions
-/

open TopologicalSpace Set Function UniformSpace WithSeminorms

open scoped BoundedContinuousFunction Topology NNReal ContDiff

variable (𝕜 E F F' : Type*) [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]
  [NormedAddCommGroup F'] [NormedSpace ℝ F'] [NormedSpace 𝕜 F'] [SMulCommClass ℝ 𝕜 F']
  {n n₁ n₂ k : ℕ∞} {K K₁ K₂ : Compacts E}

structure ContDiffMapSupportedIn (n : ℕ∞) (K : Compacts E) : Type _ where
  /-- The underlying function. Use coercion instead. -/
  protected toFun : E → F
  protected contDiff' : ContDiff ℝ n toFun
  protected zero_on_compl' : EqOn toFun 0 Kᶜ

scoped[Distributions] notation "𝓓^{" n "}_{" K "}(" E ", " F ")" =>

  ContDiffMapSupportedIn E F n K

scoped[Distributions] notation "𝓓_{" K "}(" E ", " F ")" =>

  ContDiffMapSupportedIn E F ⊤ K

open Distributions

class ContDiffMapSupportedInClass (B : Type*) (E F : outParam <| Type*)
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F]
    (n : outParam ℕ∞) (K : outParam <| Compacts E)
    extends FunLike B E F where
  map_contDiff (f : B) : ContDiff ℝ n f
  map_zero_on_compl (f : B) : EqOn f 0 Kᶜ

open ContDiffMapSupportedInClass

namespace ContDiffMapSupportedInClass

-- INSTANCE (free from Core): (B

-- INSTANCE (free from Core): (B

end ContDiffMapSupportedInClass

namespace ContDiffMapSupportedIn

-- INSTANCE (free from Core): toContDiffMapSupportedInClass

variable {E F F'}

protected theorem contDiff (f : 𝓓^{n}_{K}(E, F)) : ContDiff ℝ n f := map_contDiff f

protected theorem zero_on_compl (f : 𝓓^{n}_{K}(E, F)) : EqOn f 0 Kᶜ := map_zero_on_compl f

protected theorem compact_supp (f : 𝓓^{n}_{K}(E, F)) : HasCompactSupport f :=
  .intro K.isCompact (map_zero_on_compl f)
