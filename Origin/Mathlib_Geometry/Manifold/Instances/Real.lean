/-
Extracted from Geometry/Manifold/Instances/Real.lean
Genuine: 1 of 6 | Dissolved: 1 | Infrastructure: 4
-/
import Origin.Core

/-!
# Constructing examples of manifolds over ℝ

We introduce the necessary bits to be able to define manifolds modelled over `ℝ^n`, boundaryless
or with boundary or with corners. As a concrete example, we construct explicitly the manifold with
boundary structure on the real interval `[x, y]`, and prove that its boundary is indeed `{x, y}`
whenever `x < y`. As a corollary, a product `M × [x, y]` with a manifold `M` without boundary
has boundary `M × {x, y}`.

More specifically, we introduce
* `modelWithCornersEuclideanHalfSpace n :
  ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n)` for the model space
  used to define `n`-dimensional real manifolds with boundary
* `modelWithCornersEuclideanQuadrant n :
  ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanQuadrant n)` for the model space used
  to define `n`-dimensional real manifolds with corners

## Notation

In the scope `Manifold`, we introduce the notations
* `𝓡 n` for the identity model with corners on `EuclideanSpace ℝ (Fin n)`
* `𝓡∂ n` for `modelWithCornersEuclideanHalfSpace n`.

For instance, if a manifold `M` is boundaryless, smooth and modelled on `EuclideanSpace ℝ (Fin m)`,
and `N` is smooth with boundary modelled on `EuclideanHalfSpace n`, and `f : M → N` is a smooth
map, then the derivative of `f` can be written simply as `mfderiv (𝓡 m) (𝓡∂ n) f` (as to why the
model with corners cannot be implicit, see the discussion in
`Geometry.Manifold.IsManifold`).

## Implementation notes

The manifold structure on the interval `[x, y] = Icc x y` requires the assumption `x < y` as a
typeclass. We provide it as `[Fact (x < y)]`.
-/

noncomputable section

open Set Function WithLp

open scoped Manifold ContDiff ENNReal

-- DISSOLVED: EuclideanHalfSpace

deriving TopologicalSpace

def EuclideanQuadrant (n : ℕ) : Type :=
  { x : EuclideanSpace ℝ (Fin n) // ∀ i : Fin n, 0 ≤ x i }

deriving TopologicalSpace

variable {n : ℕ}

-- INSTANCE (free from Core): {n

-- INSTANCE (free from Core): {n

-- INSTANCE (free from Core): [NeZero

-- INSTANCE (free from Core): :
