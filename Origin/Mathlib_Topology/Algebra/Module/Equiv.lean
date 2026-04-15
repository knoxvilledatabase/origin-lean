/-
Extracted from Topology/Algebra/Module/Equiv.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Continuous linear equivalences

Continuous semilinear / linear / star-linear equivalences between topological modules are denoted
by `M ≃SL[σ] M₂`, `M ≃L[R] M₂` and `M ≃L⋆[R] M₂`.
-/

assert_not_exists TrivialStar

open LinearMap (ker range)

open Topology Filter Pointwise

open scoped Ring

universe u v w u'

structure ContinuousLinearEquiv {R : Type*} {S : Type*} [Semiring R] [Semiring S] (σ : R →+* S)
    {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (M : Type*) [TopologicalSpace M]
    [AddCommMonoid M] (M₂ : Type*) [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M]
    [Module S M₂] extends M ≃ₛₗ[σ] M₂ where
  continuous_toFun : Continuous toFun := by first | fun_prop | dsimp; fun_prop
  continuous_invFun : Continuous invFun := by first | fun_prop | dsimp; fun_prop

attribute [inherit_doc ContinuousLinearEquiv] ContinuousLinearEquiv.continuous_toFun

ContinuousLinearEquiv.continuous_invFun
