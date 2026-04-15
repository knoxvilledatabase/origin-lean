/-
Extracted from LinearAlgebra/PiTensorProduct/DirectSum.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Tensor products of direct sums

This file shows that taking `PiTensorProduct`s commutes with taking `DirectSum`s in all arguments.

## Main results

* `ofDirectSumEquiv`: the linear equivalence between a `PiTensorProduct` of `DirectSum`s
  and the `DirectSum` of the `PiTensorProduct`s.
-/

namespace PiTensorProduct

open PiTensorProduct DirectSum TensorProduct

variable {R ι : Type*} {κ : ι → Type*} {M : (i : ι) → κ i → Type*}
  [CommSemiring R] [Π i (j : κ i), AddCommMonoid (M i j)] [Π i (j : κ i), Module R (M i j)]

open scoped Classical in

noncomputable def ofDirectSumEquiv [Finite ι] :
    (⨂[R] i, (⨁ j : κ i, M i j)) ≃ₗ[R] ⨁ p : Π i, κ i, ⨂[R] i, M i (p i) :=
  have : Fintype ι := Fintype.ofFinite ι
  ofDFinsuppEquiv

set_option backward.isDefEq.respectTransparency false in
