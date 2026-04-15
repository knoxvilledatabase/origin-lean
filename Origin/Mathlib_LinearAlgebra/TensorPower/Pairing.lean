/-
Extracted from LinearAlgebra/TensorPower/Pairing.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The pairing between the tensor power of the dual and the tensor power

We construct the pairing
`TensorPower.pairingDual : ⨂[R]^n (Module.Dual R M) →ₗ[R] (Module.Dual R (⨂[R]^n M))`.

-/

open TensorProduct PiTensorProduct

namespace TensorPower

variable (R : Type*) (M : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M]
  (n : ℕ)

noncomputable def multilinearMapToDual :
    MultilinearMap R (fun (_ : Fin n) ↦ Module.Dual R M)
      (Module.Dual R (⨂[R]^n M)) :=
  have : ∀ (_ : DecidableEq (Fin n)) (f : Fin n → Module.Dual R M)
      (φ : Module.Dual R M) (i j : Fin n) (v : Fin n → M),
      (Function.update f i φ) j (v j) =
      Function.update (fun j ↦ f j (v j)) i (φ (v i)) j := fun _ f φ i j v ↦ by
    by_cases h : j = i
    · subst h
      simp only [Function.update_self]
    · simp only [Function.update_of_ne h]
  { toFun := fun f ↦ PiTensorProduct.lift
      (MultilinearMap.compLinearMap (MultilinearMap.mkPiRing R (Fin n) 1) f)
    map_update_add' := fun f i φ₁ φ₂ ↦ by
      ext v
      dsimp
      simp only [lift.tprod, MultilinearMap.compLinearMap_apply, this,
        LinearMap.add_apply, MultilinearMap.map_update_add]
    map_update_smul' := fun f i a φ ↦ by
      ext v
      dsimp
      simp only [lift.tprod, MultilinearMap.compLinearMap_apply, this,
         LinearMap.smul_apply, MultilinearMap.map_update_smul]
      dsimp }

variable {R M n} in
