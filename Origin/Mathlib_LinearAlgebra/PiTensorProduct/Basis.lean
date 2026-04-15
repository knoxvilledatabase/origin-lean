/-
Extracted from LinearAlgebra/PiTensorProduct/Basis.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Basis for `PiTensorProduct`

This file constructs a basis for `PiTensorProduct` given bases on the component spaces.
-/

section PiTensorProduct

attribute [local ext] PiTensorProduct.ext

open LinearMap PiTensorProduct Module TensorProduct

variable {ι R : Type*} {M : ι → Type*} {κ : ι → Type*} [CommSemiring R] [∀ i, AddCommMonoid (M i)]
  [∀ i, Module R (M i)]

open Classical in

noncomputable def Basis.piTensorProduct [Finite ι] (b : Π i, Basis (κ i) R (M i)) :
    Basis (Π i, κ i) R (⨂[R] i, M i) :=
  haveI := Fintype.ofFinite ι
  Finsupp.basisSingleOne.map
    ((PiTensorProduct.congr (fun i ↦ (b i).repr)) ≪≫ₗ
      ofFinsuppEquiv ≪≫ₗ
      Finsupp.lcongr (Equiv.refl _) (constantBaseRingEquiv _ R).toLinearEquiv).symm
