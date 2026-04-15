/-
Extracted from AlgebraicGeometry/Scheme.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# The category of schemes

A scheme is a locally ringed space such that every point is contained in some open set
where there is an isomorphism of presheaves between the restriction to that open set,
and the structure sheaf of `Spec R`, for some commutative ring `R`.

A morphism of schemes is just a morphism of the underlying locally ringed spaces.

-/

universe u

noncomputable section

open TopologicalSpace CategoryTheory TopCat Opposite

namespace AlgebraicGeometry

structure Scheme extends LocallyRingedSpace where
  local_affine :
    ∀ x : toLocallyRingedSpace,
      ∃ (U : OpenNhds x) (R : CommRingCat),
        Nonempty
          (toLocallyRingedSpace.restrict U.isOpenEmbedding ≅ Spec.toLocallyRingedSpace.obj (op R))

namespace Scheme

-- INSTANCE (free from Core): :

open Lean PrettyPrinter.Delaborator SubExpr in
