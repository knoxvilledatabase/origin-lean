/-
Extracted from Analysis/Calculus/ContDiff/FTaylorSeries.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Iterated derivatives of a function

In this file, we define iteratively the `n+1`-th derivative of a function as the
derivative of the `n`-th derivative. It is called `iteratedFDeriv 𝕜 n f x` where `𝕜` is the
field, `n` is the number of iterations, `f` is the function and `x` is the point, and it is given
as an `n`-multilinear map. We also define a version `iteratedFDerivWithin` relative to a domain.
Note that, in domains, there may be several choices of possible derivative, so we make some
arbitrary choice in the definition.

We also define a predicate `HasFTaylorSeriesUpTo` (and its localized version
`HasFTaylorSeriesUpToOn`), saying that a sequence of multilinear maps is *a* sequence of
derivatives of `f`. Contrary to `iteratedFDerivWithin`, it accommodates well the
non-uniqueness of derivatives.

## Main definitions and results

Let `f : E → F` be a map between normed vector spaces over a nontrivially normed field `𝕜`.

* `HasFTaylorSeriesUpTo n f p`: expresses that the formal multilinear series `p` is a sequence
  of iterated derivatives of `f`, up to the `n`-th term (where `n` is a natural number or `∞`).
* `HasFTaylorSeriesUpToOn n f p s`: same thing, but inside a set `s`. The notion of derivative
  is now taken inside `s`. In particular, derivatives don't have to be unique.

* `iteratedFDerivWithin 𝕜 n f s x` is an `n`-th derivative of `f` over the field `𝕜` on the
  set `s` at the point `x`. It is a continuous multilinear map from `E^n` to `F`, defined as a
  derivative within `s` of `iteratedFDerivWithin 𝕜 (n-1) f s` if one exists, and `0` otherwise.
* `iteratedFDeriv 𝕜 n f x` is the `n`-th derivative of `f` over the field `𝕜` at the point `x`.
  It is a continuous multilinear map from `E^n` to `F`, defined as a derivative of
  `iteratedFDeriv 𝕜 (n-1) f` if one exists, and `0` otherwise.


### Side of the composition, and universe issues

With a naïve direct definition, the `n`-th derivative of a function belongs to the space
`E →L[𝕜] (E →L[𝕜] (E ... F)...)))` where there are n iterations of `E →L[𝕜]`. This space
may also be seen as the space of continuous multilinear functions on `n` copies of `E` with
values in `F`, by uncurrying. This is the point of view that is usually adopted in textbooks,
and that we also use. This means that the definition and the first proofs are slightly involved,
as one has to keep track of the uncurrying operation. The uncurrying can be done from the
left or from the right, amounting to defining the `n+1`-th derivative either as the derivative of
the `n`-th derivative, or as the `n`-th derivative of the derivative.
For proofs, it would be more convenient to use the latter approach (from the right),
as it means to prove things at the `n+1`-th step we only need to understand well enough the
derivative in `E →L[𝕜] F` (contrary to the approach from the left, where one would need to know
enough on the `n`-th derivative to deduce things on the `n+1`-th derivative).

However, the definition from the right leads to a universe polymorphism problem: if we define
`iteratedFDeriv 𝕜 (n + 1) f x = iteratedFDeriv 𝕜 n (fderiv 𝕜 f) x` by induction, we need to
generalize over all spaces (as `f` and `fderiv 𝕜 f` don't take values in the same space). It is
only possible to generalize over all spaces in some fixed universe in an inductive definition.
For `f : E → F`, then `fderiv 𝕜 f` is a map `E → (E →L[𝕜] F)`. Therefore, the definition will only
work if `F` and `E →L[𝕜] F` are in the same universe.

This issue does not appear with the definition from the left, where one does not need to generalize
over all spaces. Therefore, we use the definition from the left. This means some proofs later on
become a little bit more complicated: to prove that a function is `C^n`, the most efficient approach
is to exhibit a formula for its `n`-th derivative and prove it is continuous (contrary to the
inductive approach where one would prove smoothness statements without giving a formula for the
derivative). In the end, this approach is still satisfactory as it is good to have formulas for the
iterated derivatives in various constructions.

One point where this explicit approach is particularly delicate is in the proof of smoothness of a
composition: there is a formula for the `n`-th derivative of a composition (Faà di Bruno's formula),
but it is very complicated, while the inductive proof is very simple. The inductive proof would
be good enough for `C^n` functions with `n ∈ ℕ ∪ {∞}` (modulo polymorphism issues, i.e., one would
need to first prove inductively the result when all spaces belong to the same universe, and then
prove the general result by lifting all the spaces to a common universe). However, it would not
work for `C^ω` functions. Therefore, we give the proof based on Faà di Bruno's formula, which is
more complicated but more general.

### Variables management

The textbook definitions and proofs use various identifications and abuse of notations, for instance
when saying that the natural space in which the derivative lives, i.e.,
`E →L[𝕜] (E →L[𝕜] ( ... →L[𝕜] F))`, is the same as a space of multilinear maps. When doing things
formally, we need to provide explicit maps for these identifications, and chase some diagrams to see
everything is compatible with the identifications. In particular, one needs to check that taking the
derivative and then doing the identification, or first doing the identification and then taking the
derivative, gives the same result. The key point for this is that taking the derivative commutes
with continuous linear equivalences. Therefore, we need to implement all our identifications with
continuous linear equivs.

## Notation

We use the notation `E [×n]→L[𝕜] F` for the space of continuous multilinear maps on `E^n` with
values in `F`. This is the space in which the `n`-th derivative of a function from `E` to `F` lives.

In this file, we denote `⊤ : ℕ∞` with `∞`.
-/

noncomputable section

open ENat NNReal Topology Filter Set Fin Filter Function

scoped[ContDiff] notation3 "ω" => (⊤ : WithTop ℕ∞)

scoped[ContDiff] notation3 "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

open scoped ContDiff Pointwise

universe u uE uF

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] {E : Type uE} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {s t u : Set E} {f f₁ : E → F} {x : E} {m n N : WithTop ℕ∞}
  {p : E → FormalMultilinearSeries 𝕜 E F}

/-! ### Functions with a Taylor series on a domain -/

structure HasFTaylorSeriesUpToOn
  (n : WithTop ℕ∞) (f : E → F) (p : E → FormalMultilinearSeries 𝕜 E F) (s : Set E) : Prop where
  zero_eq : ∀ x ∈ s, (p x 0).curry0 = f x
  protected fderivWithin : ∀ m : ℕ, m < n → ∀ x ∈ s,
    HasFDerivWithinAt (p · m) (p x m.succ).curryLeft s x
  cont : ∀ m : ℕ, m ≤ n → ContinuousOn (p · m) s

theorem HasFTaylorSeriesUpToOn.zero_eq' (h : HasFTaylorSeriesUpToOn n f p s) {x : E} (hx : x ∈ s) :
    p x 0 = (continuousMultilinearCurryFin0 𝕜 E F).symm (f x) := by
  rw [← h.zero_eq x hx]
  exact (p x 0).uncurry0_curry0.symm
