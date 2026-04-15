/-
Extracted from LinearAlgebra/RootSystem/Finite/CanonicalBilinear.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The canonical bilinear form on a finite root pairing
Given a finite root pairing, we define a canonical map from weight space to coweight space, and the
corresponding bilinear form. This form is symmetric and Weyl-invariant, and if the base ring is
linearly ordered, then the form is root-positive, positive-semidefinite on the weight space, and
positive-definite on the span of roots.
From these facts, it is easy to show that Coxeter weights in a finite root pairing are bounded
above by 4. Thus, the pairings of roots and coroots in a crystallographic root pairing are
restricted to a small finite set of possibilities.
Another application is to the faithfulness of the Weyl group action on roots, and finiteness of the
Weyl group.

## Main definitions:
* `RootPairing.Polarization`: A distinguished linear map from the weight space to the coweight
  space.
* `RootPairing.RootForm` : The bilinear form on weight space corresponding to `Polarization`.

## Main results:
* `RootPairing.rootForm_self_sum_of_squares` : The inner product of any
  weight vector is a sum of squares.
* `RootPairing.rootForm_reflection_reflection_apply` : `RootForm` is invariant with respect
  to reflections.
* `RootPairing.rootForm_self_smul_coroot`: The inner product of a root with itself
  times the corresponding coroot is equal to two times Polarization applied to the root.
* `RootPairing.exists_ge_zero_eq_rootForm`: `RootForm` is positive semidefinite.

## References:
* [N. Bourbaki, *Lie groups and Lie algebras. Chapters 4--6*][bourbaki1968]
* [M. Demazure, *SGA III, Exposé XXI, Données Radicielles*][demazure1970]

-/

open Set Function

open Module hiding reflection

open Submodule (span)

noncomputable section

variable {ι R M N : Type*}

namespace RootPairing

variable [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N)

section Fintype

variable [Fintype ι]

def Polarization : M →ₗ[R] N :=
  ∑ i, LinearMap.toSpanSingleton R N (P.coroot i) ∘ₗ P.coroot' i
