/-
Extracted from Analysis/Analytic/Inverse.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Inverse of analytic functions

We construct the left and right inverse of a formal multilinear series with invertible linear term,
we prove that they coincide and study their properties (notably convergence). We deduce that the
inverse of an analytic open partial homeomorphism is analytic.

## Main statements

* `p.leftInv i x`: the formal left inverse of the formal multilinear series `p`, with constant
  coefficient `x`, for `i : E ≃L[𝕜] F` which coincides with `p₁`.
* `p.rightInv i x`: the formal right inverse of the formal multilinear series `p`, with constant
  coefficient `x`, for `i : E ≃L[𝕜] F` which coincides with `p₁`.
* `p.leftInv_comp` says that `p.leftInv i x` is indeed a left inverse to `p` when `p₁ = i`.
* `p.rightInv_comp` says that `p.rightInv i x` is indeed a right inverse to `p` when `p₁ = i`.
* `p.leftInv_eq_rightInv`: the two inverses coincide.
* `p.radius_rightInv_pos_of_radius_pos`: if a power series has a positive radius of convergence,
  then so does its inverse.

* `OpenPartialHomeomorph.hasFPowerSeriesAt_symm` shows that, if an open partial homeomorph has a
  power series `p` at a point, with invertible linear part, then the inverse also has a power series
  at the image point, given by `p.leftInv`.
-/

open scoped Topology ENNReal

open Finset Filter

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

namespace FormalMultilinearSeries

/-! ### The left inverse of a formal multilinear series -/

noncomputable def leftInv (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E) :
    FormalMultilinearSeries 𝕜 F E
  | 0 => ContinuousMultilinearMap.uncurry0 𝕜 _ x
  | 1 => (continuousMultilinearCurryFin1 𝕜 F E).symm i.symm
  | n + 2 =>
    -∑ c : { c : Composition (n + 2) // c.length < n + 2 },
        (leftInv p i x (c : Composition (n + 2)).length).compAlongComposition
          (p.compContinuousLinearMap i.symm) c
