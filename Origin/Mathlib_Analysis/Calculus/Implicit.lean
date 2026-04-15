/-
Extracted from Analysis/Calculus/Implicit.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Implicit function theorem

We prove three versions of the implicit function theorem. First we define a structure
`ImplicitFunctionData` that holds arguments for the most general version of the implicit function
theorem, see `ImplicitFunctionData.implicitFunction` and
`ImplicitFunctionData.hasStrictFDerivAt_implicitFunction`. This version allows a user to choose a
specific implicit function but provides only a little convenience over the inverse function theorem.

Then we define `HasStrictFDerivAt.implicitFunctionDataOfComplemented`: implicit function defined by
`f (g z y) = z`, where `f : E → F` is a function strictly differentiable at `a` such that its
derivative `f'` is surjective and has a `complemented` kernel.

Finally, if the codomain of `f` is a finite-dimensional space, then we can automatically prove
that the kernel of `f'` is complemented, hence the only assumptions are `HasStrictFDerivAt`
and `f'.range = ⊤`. This version is named `HasStrictFDerivAt.implicitFunction`.

For the version where the implicit equation is defined by a $C^n$ function `f : E × F → G` with an
invertible derivative `∂f/∂y`, see `ContDiffAt.implicitFunction`.

## TODO

* Add a version for `f : 𝕜 × 𝕜 → 𝕜` proving `HasStrictDerivAt` and `deriv φ = ...`.
* Prove that in a real vector space the implicit function has the same smoothness as the original
  one.
* If the original function is differentiable in a neighborhood, then the implicit function is
  differentiable in a neighborhood as well. Current setup only proves differentiability at one
  point for the implicit function constructed in this file (as opposed to an unspecified implicit
  function). One of the ways to overcome this difficulty is to use uniqueness of the implicit
  function in the general version of the theorem. Another way is to prove that *any* implicit
  function satisfying some predicate is strictly differentiable.

## Tags

implicit function, inverse function
-/

noncomputable section

open scoped Topology

open Filter

open ContinuousLinearMap (fst snd smulRight ker_prod)

open ContinuousLinearEquiv (ofBijective)

open LinearMap (ker range)

/-!
### General version

Consider two functions `f : E → F` and `g : E → G` and a point `a` such that

* both functions are strictly differentiable at `a`;
* the derivatives are surjective;
* the kernels of the derivatives are complementary subspaces of `E`.

Note that the map `x ↦ (f x, g x)` has a bijective derivative, hence it is an open partial
homeomorphism between `E` and `F × G`. We use this fact to define a function `φ : F → G → E`
(see `ImplicitFunctionData.implicitFunction`) such that for `(y, z)` close enough to `(f a, g a)`
we have `f (φ y z) = y` and `g (φ y z) = z`. We also prove a formula for `∂φ / ∂z`.

Though this statement is almost symmetric with respect to `F`, `G`, we interpret it in the following
way. Consider a family of surfaces `{x | f x = y}`, `y ∈ 𝓝 (f a)`. Each of these surfaces is
parametrized by `φ y`.

There are many ways to choose a (differentiable) function `φ` such that `f (φ y z) = y` but the
extra condition `g (φ y z) = z` allows a user to select one of these functions. If we imagine
that the level surfaces `f = const` form a local horizontal foliation, then the choice of
`g` fixes a transverse foliation `g = const`, and `φ` is the inverse function of the projection
of `{x | f x = y}` along this transverse foliation.

This version of the theorem is used to prove the other versions and can be used if a user
needs to have a complete control over the choice of the implicit function.
-/

structure ImplicitFunctionData (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : Type*)
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] (F : Type*) [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] [CompleteSpace F] (G : Type*) [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    [CompleteSpace G] where
  /-- Left function -/
  leftFun : E → F
  /-- Derivative of the left function -/
  leftDeriv : E →L[𝕜] F
  /-- Right function -/
  rightFun : E → G
  /-- Derivative of the right function -/
  rightDeriv : E →L[𝕜] G
  /-- The point at which `leftFun` and `rightFun` are strictly differentiable -/
  pt : E
  hasStrictFDerivAt_leftFun : HasStrictFDerivAt leftFun leftDeriv pt
  hasStrictFDerivAt_rightFun : HasStrictFDerivAt rightFun rightDeriv pt
  range_leftDeriv : leftDeriv.range = ⊤
  range_rightDeriv : rightDeriv.range = ⊤
  isCompl_ker : IsCompl leftDeriv.ker rightDeriv.ker

namespace ImplicitFunctionData

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [CompleteSpace E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [CompleteSpace F] {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]
  (φ : ImplicitFunctionData 𝕜 E F G)

def prodFun (x : E) : F × G :=
  (φ.leftFun x, φ.rightFun x)
