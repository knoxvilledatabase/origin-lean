/-
Extracted from LinearAlgebra/Multilinear/Finsupp.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Interactions between finitely-supported functions and multilinear maps

## Main definitions

* `freeFinsuppEquiv` is an equivalence of multilinear maps over free modules with finitely
  supported maps.

-/

variable {ι ι' R : Type*} {κ : ι → Type*}

namespace MultilinearMap

section freeFinsuppEquiv

variable [DecidableEq ι] [Fintype ι] [CommSemiring R] [DecidableEq R]
  [DecidableEq ι'] [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]

noncomputable def freeFinsuppEquiv :
    (((Π i, κ i) × ι') →₀ R) ≃ₗ[R] MultilinearMap R (fun i => (κ i →₀ R)) (ι' →₀ R) :=
  (finsuppLequivDFinsupp R) ≪≫ₗ freeDFinsuppEquiv ≪≫ₗ
  ((finsuppLequivDFinsupp R).multilinearMapCongrRight R).symm ≪≫ₗ
  LinearEquiv.multilinearMapCongrLeft (fun _ => finsuppLequivDFinsupp R)
