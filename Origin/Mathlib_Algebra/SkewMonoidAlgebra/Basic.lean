/-
Extracted from Algebra/SkewMonoidAlgebra/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Skew Monoid Algebras

Given a monoid `G` acting on a ring `k`, the skew monoid algebra of `G` over `k` is the set
of finitely supported functions `f : G → k` for which addition is defined pointwise and
multiplication of two elements `f` and `g` is given by the finitely supported function whose
value at `a` is the sum of `f x * (x • g y)` over all pairs `x, y` such that `x * y = a`,
where `•` denotes the action of `G` on `k`. When this action is trivial, this product is
the usual convolution product.

In fact the construction of the skew monoid algebra makes sense when `G` is not even a monoid, but
merely a magma, i.e., when `G` carries a multiplication which is not required to satisfy any
conditions at all, and `k` is a not-necessarily-associative semiring. In this case the construction
yields a not-necessarily-unital, not-necessarily-associative algebra.

## Main Definitions
- `SkewMonoidAlgebra k G`: the skew monoid algebra of `G` over `k` is the type of finite formal
  `k`-linear combinations of terms of `G`, endowed with a skewed convolution product.

-/

noncomputable section

structure SkewMonoidAlgebra (k : Type*) (G : Type*) [Zero k] where
  /-- The natural map from `G →₀ k` to `SkewMonoidAlgebra k G`. -/
  ofFinsupp ::
  /-- The natural map from `SkewMonoidAlgebra k G` to `G →₀ k`. -/
  toFinsupp : G →₀ k

open Function

namespace SkewMonoidAlgebra

variable {k G : Type*}

section AddMonoid

variable [AddMonoid k]
