/-
Extracted from Topology/Algebra/Module/LinearMap.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Continuous linear maps

In this file we define continuous (semi-)linear maps, as semilinear maps between topological
modules which are continuous. The set of continuous semilinear maps between the topological
`R₁`-module `M` and `R₂`-module `M₂` with respect to the `RingHom` `σ` is denoted by `M →SL[σ] M₂`.
Plain linear maps are denoted by `M →L[R] M₂` and star-linear maps by `M →L⋆[R] M₂`.
-/

assert_not_exists TrivialStar

open LinearMap (ker range)

open Topology Filter Pointwise

universe u v w u'

structure ContinuousLinearMap {R : Type*} {S : Type*} [Semiring R] [Semiring S] (σ : R →+* S)
    (M : Type*) [TopologicalSpace M] [AddCommMonoid M] (M₂ : Type*) [TopologicalSpace M₂]
    [AddCommMonoid M₂] [Module R M] [Module S M₂] extends M →ₛₗ[σ] M₂ where
  cont : Continuous toFun := by fun_prop

attribute [inherit_doc ContinuousLinearMap] ContinuousLinearMap.cont
