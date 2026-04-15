/-
Extracted from LinearAlgebra/CliffordAlgebra/Fold.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Recursive computation rules for the Clifford algebra

This file provides API for a special case `CliffordAlgebra.foldr` of the universal property
`CliffordAlgebra.lift` with `A = Module.End R N` for some arbitrary module `N`. This specialization
resembles the `list.foldr` operation, allowing a bilinear map to be "folded" along the generators.

For convenience, this file also provides `CliffordAlgebra.foldl`, implemented via
`CliffordAlgebra.reverse`

## Main definitions

* `CliffordAlgebra.foldr`: a computation rule for building linear maps out of the clifford
  algebra starting on the right, analogous to using `list.foldr` on the generators.
* `CliffordAlgebra.foldl`: a computation rule for building linear maps out of the clifford
  algebra starting on the left, analogous to using `list.foldl` on the generators.

## Main statements

* `CliffordAlgebra.right_induction`: an induction rule that adds generators from the right.
* `CliffordAlgebra.left_induction`: an induction rule that adds generators from the left.
-/

universe u1 u2 u3

variable {R M N : Type*}

variable [CommRing R] [AddCommGroup M] [AddCommGroup N]

variable [Module R M] [Module R N]

variable (Q : QuadraticForm R M)

namespace CliffordAlgebra

section Foldr

def foldr (f : M →ₗ[R] N →ₗ[R] N) (hf : ∀ m x, f m (f m x) = Q m • x) :
    N →ₗ[R] CliffordAlgebra Q →ₗ[R] N :=
  (CliffordAlgebra.lift Q ⟨f, fun v => LinearMap.ext <| hf v⟩).toLinearMap.flip
