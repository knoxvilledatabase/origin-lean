/-
Extracted from Analysis/Distribution/TestFunction.lean
Genuine: 5 of 8 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Continuously differentiable functions with compact support

This file develops the basic theory of bundled `n`-times continuously differentiable functions
with compact support contained in some open set `Ω`. More explicitly, given normed spaces `E`
and `F`, an open set `Ω : Opens E` and `n : ℕ∞`, we are interested in the space `𝓓^{n}(Ω, F)` of
maps `f : E → F` such that:

- `f` is `n`-times continuously differentiable: `ContDiff ℝ n f`.
- `f` has compact support: `HasCompactSupport f`.
- the support of `f` is inside the open set `Ω`: `tsupport f ⊆ Ω`.

This exists as a bundled type to equip it with the canonical LF topology induced by the inclusions
`𝓓_{K}^{n}(Ω, F) → 𝓓^{n}(Ω, F)` (see `ContDiffMapSupportedIn`). The dual space is then the space of
distributions, or "weak solutions" to PDEs, on `Ω`.

## Main definitions

- `TestFunction Ω F n`: the type of bundled `n`-times continuously differentiable
  functions `E → F` with compact support contained in `Ω`.
- `TestFunction.topologicalSpace`: the canonical LF topology on `𝓓^{n}(Ω, F)`. It is the
  locally convex inductive limit of the topologies on each `𝓓_{K}^{n}(Ω, F)`.

## Main statements

- `TestFunction.continuous_iff_continuous_comp`: a linear map from `𝓓^{n}(E, F)`
  to a locally convex space is continuous iff its restriction to `𝓓^{n}_{K}(E, F)` is
  continuous for each compact set `K`. We will later translate this concretely in terms
  of seminorms.

## Notation

- `𝓓^{n}(Ω, F)`: the space of bundled `n`-times continuously differentiable functions `E → F`
  with compact support contained in `Ω`.
- `𝓓(Ω, F)`: the space of bundled smooth (infinitely differentiable) functions `E → F`
  with compact support contained in `Ω`, i.e. `𝓓^{⊤}(Ω, F)`.

## Tags

distributions, test function
-/

open Function Seminorm SeminormFamily Set TopologicalSpace UniformSpace

open scoped BoundedContinuousFunction NNReal Topology ContDiff

variable {𝕜 𝕂 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω Ω₁ Ω₂ : Opens E}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [NormedSpace 𝕜 F']
  {n n₁ n₂ k : ℕ∞}

variable (Ω F n) in

structure TestFunction : Type _ where
  /-- The underlying function. Use coercion instead. -/
  protected toFun : E → F
  protected contDiff' : ContDiff ℝ n toFun
  protected hasCompactSupport' : HasCompactSupport toFun
  protected tsupport_subset' : tsupport toFun ⊆ Ω

scoped[Distributions] notation "𝓓^{" n "}(" Ω ", " F ")" => TestFunction Ω F n

scoped[Distributions] notation "𝓓(" Ω ", " F ")" => TestFunction Ω F ⊤

open Distributions

class TestFunctionClass (B : Type*)
    {E : outParam <| Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (Ω : outParam <| Opens E)
    (F : outParam <| Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (n : outParam ℕ∞) extends FunLike B E F where
  map_contDiff (f : B) : ContDiff ℝ n f
  map_hasCompactSupport (f : B) : HasCompactSupport f
  tsupport_map_subset (f : B) : tsupport f ⊆ Ω

open TestFunctionClass

namespace TestFunctionClass

-- INSTANCE (free from Core): (B

-- INSTANCE (free from Core): (B

end TestFunctionClass

namespace TestFunction

-- INSTANCE (free from Core): toTestFunctionClass

protected theorem contDiff (f : 𝓓^{n}(Ω, F)) : ContDiff ℝ n f := map_contDiff f

protected theorem hasCompactSupport (f : 𝓓^{n}(Ω, F)) : HasCompactSupport f :=
  map_hasCompactSupport f

protected theorem tsupport_subset (f : 𝓓^{n}(Ω, F)) : tsupport f ⊆ Ω := tsupport_map_subset f
