/-
Extracted from Analysis/Calculus/BumpFunction/Basic.lean
Genuine: 6 of 7 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Infinitely smooth "bump" functions

A smooth bump function is an infinitely smooth function `f : E → ℝ` supported on a ball
that is equal to `1` on a ball of smaller radius.

These functions have many uses in real analysis. E.g.,

- they can be used to construct a smooth partition of unity which is a very useful tool;
- they can be used to approximate a continuous function by infinitely smooth functions.

There are two classes of spaces where bump functions are guaranteed to exist:
inner product spaces and finite-dimensional spaces.

In this file we define a typeclass `HasContDiffBump`
saying that a normed space has a family of smooth bump functions with certain properties.

We also define a structure `ContDiffBump` that holds the center and radii of the balls from above.
An element `f : ContDiffBump c` can be coerced to a function which is an infinitely smooth function
such that

- `f` is equal to `1` in `Metric.closedBall c f.rIn`;
- `support f = Metric.ball c f.rOut`;
- `0 ≤ f x ≤ 1` for all `x`.

## Main Definitions

- `ContDiffBump (c : E)`: a structure holding data needed to construct
  an infinitely smooth bump function.
- `ContDiffBumpBase (E : Type*)`: a family of infinitely smooth bump functions
  that can be used to construct coercion of a `ContDiffBump (c : E)`
  to a function.
- `HasContDiffBump (E : Type*)`: a typeclass saying that `E` has a `ContDiffBumpBase`.
  Two instances of this typeclass (for inner product spaces and for finite-dimensional spaces)
  are provided elsewhere.

## Keywords

smooth function, smooth bump function
-/

noncomputable section

open Function Set Filter

open scoped Topology Filter ContDiff

variable {E X : Type*}

structure ContDiffBump (c : E) where
  /-- real numbers `0 < rIn < rOut` -/
  (rIn rOut : ℝ)
  rIn_pos : 0 < rIn
  rIn_lt_rOut : rIn < rOut

structure ContDiffBumpBase (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  /-- The function underlying this family of bump functions -/
  toFun : ℝ → E → ℝ
  mem_Icc : ∀ (R : ℝ) (x : E), toFun R x ∈ Icc (0 : ℝ) 1
  symmetric : ∀ (R : ℝ) (x : E), toFun R (-x) = toFun R x
  smooth : ContDiffOn ℝ ∞ (uncurry toFun) (Ioi (1 : ℝ) ×ˢ (univ : Set E))
  eq_one : ∀ R : ℝ, 1 < R → ∀ x : E, ‖x‖ ≤ 1 → toFun R x = 1
  support : ∀ R : ℝ, 1 < R → Function.support (toFun R) = Metric.ball (0 : E) R

class HasContDiffBump (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop where
  out : Nonempty (ContDiffBumpBase E)

def someContDiffBumpBase (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [hb : HasContDiffBump E] : ContDiffBumpBase E :=
  Nonempty.some hb.out

namespace ContDiffBump

theorem rOut_pos {c : E} (f : ContDiffBump c) : 0 < f.rOut :=
  f.rIn_pos.trans f.rIn_lt_rOut

theorem one_lt_rOut_div_rIn {c : E} (f : ContDiffBump c) : 1 < f.rOut / f.rIn := by
  rw [one_lt_div f.rIn_pos]
  exact f.rIn_lt_rOut

-- INSTANCE (free from Core): (c

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup X] [NormedSpace ℝ X]
  [HasContDiffBump E] {c : E} (f : ContDiffBump c) {x : E} {n : ℕ∞}
