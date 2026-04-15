/-
Extracted from LinearAlgebra/PiTensorProduct/DFinsupp.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Tensor products of finitely supported functions

This file shows that taking `PiTensorProduct`s commutes with taking `DFinsupp`s in all arguments.

## Main results

* `ofDFinsuppEquiv`: the linear equivalence between a `PiTensorProduct` of `DFinsupp`s
  and the `DFinsupp` of the `PiTensorProduct`s.
-/

namespace PiTensorProduct

open LinearMap TensorProduct

variable {R ι : Type*} {κ : ι → Type*} {M : (i : ι) → κ i → Type*}
  [CommSemiring R] [Π i (j : κ i), AddCommMonoid (M i j)] [Π i (j : κ i), Module R (M i j)]
  [Fintype ι] [DecidableEq ι] [(i : ι) → DecidableEq (κ i)]

def ofDFinsuppEquiv :
    (⨂[R] i, (Π₀ j : κ i, M i j)) ≃ₗ[R] Π₀ p : Π i, κ i, ⨂[R] i, M i (p i) :=
  LinearEquiv.ofLinear
    (lift <| MultilinearMap.fromDFinsuppEquiv κ R
      fun p ↦ (DFinsupp.lsingle p).compMultilinearMap (tprod R))
    (DFinsupp.lsum R fun p ↦ lift <|
      (PiTensorProduct.map fun i ↦ DFinsupp.lsingle (p i)).compMultilinearMap (tprod R))
    (by ext p x; simp)
    (by ext x; simp)
