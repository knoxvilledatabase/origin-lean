/-
Extracted from Combinatorics/Additive/AP/Three/Behrend.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Behrend's bound on Roth numbers

This file proves Behrend's lower bound on Roth numbers. This says that we can find a subset of
`{1, ..., n}` of size `n / exp (O (sqrt (log n)))` which does not contain arithmetic progressions of
length `3`.

The idea is that the sphere (in the `n`-dimensional Euclidean space) doesn't contain arithmetic
progressions (literally) because the corresponding ball is strictly convex. Thus we can take
integer points on that sphere and map them onto `ℕ` in a way that preserves arithmetic progressions
(`Behrend.map`).

## Main declarations

* `Behrend.sphere`: The intersection of the Euclidean sphere with the positive integer quadrant.
  This is the set that we will map on `ℕ`.
* `Behrend.map`: Given a natural number `d`, `Behrend.map d : ℕⁿ → ℕ` reads off the coordinates as
  digits in base `d`.
* `Behrend.card_sphere_le_rothNumberNat`: Implicit lower bound on Roth numbers in terms of
  `Behrend.sphere`.
* `Behrend.roth_lower_bound`: Behrend's explicit lower bound on Roth numbers.

## References

* [Bryan Gillespie, *Behrend’s Construction*]
  (http://www.epsilonsmall.com/resources/behrends-construction/behrend.pdf)
* Behrend, F. A., "On sets of integers which contain no three terms in arithmetical progression"
* [Wikipedia, *Salem-Spencer set*](https://en.wikipedia.org/wiki/Salem–Spencer_set)

## Tags

3AP-free, Salem-Spencer, Behrend construction, arithmetic progression, sphere, strictly convex
-/

assert_not_exists IsConformalMap Conformal

open Nat hiding log

open Finset Metric Real WithLp

open scoped Pointwise

lemma threeAPFree_frontier {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [TopologicalSpace E]
    [AddCommMonoid E] [Module 𝕜 E] {s : Set E} (hs₀ : IsClosed s) (hs₁ : StrictConvex 𝕜 s) :
    ThreeAPFree (frontier s) := by
  intro a ha b hb c hc habc
  obtain rfl : (1 / 2 : 𝕜) • a + (1 / 2 : 𝕜) • c = b := by
    rwa [← smul_add, one_div, inv_smul_eq_iff₀ (show (2 : 𝕜) ≠ 0 by simp), two_smul]
  have :=
    hs₁.eq (hs₀.frontier_subset ha) (hs₀.frontier_subset hc) one_half_pos one_half_pos
      (add_halves _) hb.2
  simp [this, ← add_smul]
  ring_nf
  simp

lemma threeAPFree_sphere {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [StrictConvexSpace ℝ E] (x : E) (r : ℝ) : ThreeAPFree (sphere x r) := by
  obtain rfl | hr := eq_or_ne r 0
  · rw [sphere_zero]
    exact threeAPFree_singleton _
  · convert threeAPFree_frontier isClosed_closedBall (strictConvex_closedBall ℝ x r)
    exact (frontier_closedBall _ hr).symm

namespace Behrend

variable {n d k N : ℕ} {x : Fin n → ℕ}

/-!
### Turning the sphere into 3AP-free set

We define `Behrend.sphere`, the intersection of the $L^2$ sphere with the positive quadrant of
integer points. Because the $L^2$ closed ball is strictly convex, the $L^2$ sphere and
`Behrend.sphere` are 3AP-free (`threeAPFree_sphere`). Then we can turn this set in
`Fin n → ℕ` into a set in `ℕ` using `Behrend.map`, which preserves `ThreeAPFree` because it is
an additive monoid homomorphism.
-/

def box (n d : ℕ) : Finset (Fin n → ℕ) :=
  Fintype.piFinset fun _ => range d

theorem mem_box : x ∈ box n d ↔ ∀ i, x i < d := by simp only [box, Fintype.mem_piFinset, mem_range]
