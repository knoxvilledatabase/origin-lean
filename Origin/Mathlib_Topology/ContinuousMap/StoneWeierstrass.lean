/-
Extracted from Topology/ContinuousMap/StoneWeierstrass.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The Stone-Weierstrass theorem

If a subalgebra `A` of `C(X, ℝ)`, where `X` is a compact topological space,
separates points, then it is dense.

We argue as follows.

* In any subalgebra `A` of `C(X, ℝ)`, if `f ∈ A`, then `abs f ∈ A.topologicalClosure`.
  This follows from the Weierstrass approximation theorem on `[-‖f‖, ‖f‖]` by
  approximating `abs` uniformly thereon by polynomials.
* This ensures that `A.topologicalClosure` is actually a sublattice:
  if it contains `f` and `g`, then it contains the pointwise supremum `f ⊔ g`
  and the pointwise infimum `f ⊓ g`.
* Any nonempty sublattice `L` of `C(X, ℝ)` which separates points is dense,
  by a nice argument approximating a given `f` above and below using separating functions.
  For each `x y : X`, we pick a function `g x y ∈ L` so `g x y x = f x` and `g x y y = f y`.
  By continuity these functions remain close to `f` on small patches around `x` and `y`.
  We use compactness to identify a certain finitely indexed infimum of finitely indexed supremums
  which is then close to `f` everywhere, obtaining the desired approximation.
* Finally we put these pieces together. `L = A.topologicalClosure` is a nonempty sublattice
  which separates points since `A` does, and so is dense (in fact equal to `⊤`).

We then prove the complex version for star subalgebras `A`, by separately approximating
the real and imaginary parts using the real subalgebra of real-valued functions in `A`
(which still separates points, by taking the norm-square of a separating function).

## Future work

Extend to cover the case of subalgebras of the continuous functions vanishing at infinity,
on non-compact spaces.

-/

assert_not_exists Unitization

noncomputable section

namespace ContinuousMap

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

open scoped Polynomial

def attachBound (f : C(X, ℝ)) : C(X, Set.Icc (-‖f‖) ‖f‖) where
  toFun x := ⟨f x, ⟨neg_norm_le_apply f x, apply_le_norm f x⟩⟩
