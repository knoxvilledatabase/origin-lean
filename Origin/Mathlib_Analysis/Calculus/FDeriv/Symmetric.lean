/-
Extracted from Analysis/Calculus/FDeriv/Symmetric.lean
Genuine: 5 of 7 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Symmetry of the second derivative

We show that, over the reals, the second derivative is symmetric.

The most precise result is `Convex.second_derivative_within_at_symmetric`. It asserts that,
if a function is differentiable inside a convex set `s` with nonempty interior, and has a second
derivative within `s` at a point `x`, then this second derivative at `x` is symmetric. Note that
this result does not require continuity of the first derivative.

The following particular cases of this statement are especially relevant:

`second_derivative_symmetric_of_eventually` asserts that, if a function is differentiable on a
neighborhood of `x`, and has a second derivative at `x`, then this second derivative is symmetric.

`second_derivative_symmetric` asserts that, if a function is differentiable, and has a second
derivative at `x`, then this second derivative is symmetric.

There statements are given over `ℝ` or `ℂ`, the general version being deduced from the real
version. We also give statements in terms of `fderiv` and `fderivWithin`, called respectively
`ContDiffAt.isSymmSndFDerivAt` and `ContDiffWithinAt.isSymmSndFDerivWithinAt` (the latter
requiring that the point under consideration is accumulated by points in the interior of the set).
These are written using ad hoc predicates `IsSymmSndFDerivAt` and `IsSymmSndFDerivWithinAt`, which
increase readability of statements in differential geometry where they show up a lot.

We also deduce statements over an arbitrary field, requiring that the function is `C^2` if the field
is `ℝ` or `ℂ`, and analytic otherwise. Formally, we assume that the function is `C^n`
with `minSmoothness 𝕜 2 ≤ n`, where `minSmoothness 𝕜 i` is `i` if `𝕜` is `ℝ` or `ℂ`,
and `ω` otherwise.

## Implementation note

For the proof, we obtain an asymptotic expansion to order two of `f (x + v + w) - f (x + v)`, by
using the mean value inequality applied to a suitable function along the
segment `[x + v, x + v + w]`. This expansion involves `f'' ⬝ w` as we move along a segment directed
by `w` (see `Convex.taylor_approx_two_segment`).

Consider the alternate sum `f (x + v + w) + f x - f (x + v) - f (x + w)`, corresponding to the
values of `f` along a rectangle based at `x` with sides `v` and `w`. One can write it using the two
sides directed by `w`, as `(f (x + v + w) - f (x + v)) - (f (x + w) - f x)`. Together with the
previous asymptotic expansion, one deduces that it equals `f'' v w + o(1)` when `v, w` tends to `0`.
Exchanging the roles of `v` and `w`, one instead gets an asymptotic expansion `f'' w v`, from which
the equality `f'' v w = f'' w v` follows.

In our most general statement, we only assume that `f` is differentiable inside a convex set `s`, so
a few modifications have to be made. Since we don't assume continuity of `f` at `x`, we consider
instead the rectangle based at `x + v + w` with sides `v` and `w`,
in `Convex.isLittleO_alternate_sum_square`, but the argument is essentially the same. It only works
when `v` and `w` both point towards the interior of `s`, to make sure that all the sides of the
rectangle are contained in `s` by convexity. The general case follows by linearity, though.
-/

open Asymptotics Set Filter

open scoped Topology ContDiff

section General

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] {s t : Set E} {f : E → F} {x : E}

variable (𝕜) in

def IsSymmSndFDerivWithinAt (f : E → F) (s : Set E) (x : E) : Prop :=
  ∀ v w, fderivWithin 𝕜 (fderivWithin 𝕜 f s) s x v w = fderivWithin 𝕜 (fderivWithin 𝕜 f s) s x w v

variable (𝕜) in

def IsSymmSndFDerivAt (f : E → F) (x : E) : Prop :=
  ∀ v w, fderiv 𝕜 (fderiv 𝕜 f) x v w = fderiv 𝕜 (fderiv 𝕜 f) x w v

lemma fderivWithin_fderivWithin_eq_of_mem_nhdsWithin (h : t ∈ 𝓝[s] x)
    (hf : ContDiffWithinAt 𝕜 2 f t x) (hs : UniqueDiffOn 𝕜 s) (ht : UniqueDiffOn 𝕜 t) (hx : x ∈ s) :
    fderivWithin 𝕜 (fderivWithin 𝕜 f s) s x = fderivWithin 𝕜 (fderivWithin 𝕜 f t) t x := by
  have A : ∀ᶠ y in 𝓝[s] x, fderivWithin 𝕜 f s y = fderivWithin 𝕜 f t y := by
    have : ∀ᶠ y in 𝓝[s] x, ContDiffWithinAt 𝕜 2 f t y :=
      nhdsWithin_le_iff.2 h (nhdsWithin_mono _ (subset_insert x t) (hf.eventually (by simp)))
    filter_upwards [self_mem_nhdsWithin, this, eventually_eventually_nhdsWithin.2 h]
      with y hy h'y h''y
    exact fderivWithin_of_mem_nhdsWithin h''y (hs y hy) (h'y.differentiableWithinAt two_ne_zero)
  have : fderivWithin 𝕜 (fderivWithin 𝕜 f s) s x = fderivWithin 𝕜 (fderivWithin 𝕜 f t) s x := by
    apply Filter.EventuallyEq.fderivWithin_eq A
    exact fderivWithin_of_mem_nhdsWithin h (hs x hx) (hf.differentiableWithinAt two_ne_zero)
  rw [this]
  apply fderivWithin_of_mem_nhdsWithin h (hs x hx)
  exact (hf.fderivWithin_right (m := 1) ht le_rfl
    (mem_of_mem_nhdsWithin hx h)).differentiableWithinAt one_ne_zero

lemma fderivWithin_fderivWithin_eq_of_eventuallyEq (h : s =ᶠ[𝓝 x] t) :
    fderivWithin 𝕜 (fderivWithin 𝕜 f s) s x = fderivWithin 𝕜 (fderivWithin 𝕜 f t) t x := calc
  fderivWithin 𝕜 (fderivWithin 𝕜 f s) s x
    = fderivWithin 𝕜 (fderivWithin 𝕜 f t) s x :=
      (fderivWithin_eventually_congr_set h).fderivWithin_eq_of_nhds
  _ = fderivWithin 𝕜 (fderivWithin 𝕜 f t) t x := fderivWithin_congr_set h

lemma fderivWithin_fderivWithin_eq_of_mem_nhds {f : E → F} {x : E} {s : Set E}
    (h : s ∈ 𝓝 x) :
    fderivWithin 𝕜 (fderivWithin 𝕜 f s) s x = fderiv 𝕜 (fderiv 𝕜 f) x := by
  simp only [← fderivWithin_univ]
  apply fderivWithin_fderivWithin_eq_of_eventuallyEq
  simp [h]
