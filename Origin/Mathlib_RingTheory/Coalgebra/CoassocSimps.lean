/-
Extracted from RingTheory/Coalgebra/CoassocSimps.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Tactic to reassociate comultiplication in a coalgebra

`coassoc_simps` is a simp set useful to prove tautologies on coalgebras.

The general algorithm it follows is to push the associators `TensorProduct.assoc` and
commutators `TensorProduct.comm` inwards (to the right) until they cancel against
co-multiplications.

The simp set makes the following choice of normal form
* It regards `TensorProduct.map`, `TensorProduct.assoc`, `TensorProduct.comm` as the primitive
  constructions and rewrites everything else such as `lTensor`, `leftComm` using them.
* It rewrites both sides into a right associated composition of linear maps.
  In particular `LinearMap.comp_assoc` and `LinearEquiv.coe_trans` are tagged.
* It rewrites `(f₂ ⊗ g₂) ∘ (f₁ ⊗ g₁)` into `(f₂ ∘ f₁) ⊗ (g₂ ∘ g₁)`.

## Notes

- It is not confluent with `(ε ⊗ₘ id) ∘ₗ δ = λ⁻¹`.
  It is often useful to `trans` (or `calc`) with a term containing
  `(ε ⊗ₘ _) ∘ₗ δ` or `(_ ⊗ₘ ε) ∘ₗ δ`,
  and use one of `map_counit_comp_comul_left` `map_counit_comp_comul_right`
  `map_counit_comp_comul_left_assoc` `map_counit_comp_comul_right_assoc` to continue.

- Some lemmas (e.g. `lid_comp_map : λ ∘ₗ (f ⊗ₘ g) = g ∘ₗ λ ∘ₗ (f ⊗ₘ id)`) loops when tagged as simp,
  so we wrap it inside a rudimentary simproc that only fires when `g ≠ id`.
-/

open TensorProduct

open LinearMap (id)

open Coalgebra

open Qq

namespace CoassocSimps

variable {R A M N P M' N' P' Q Q' M₁ M₂ M₃ N₁ N₂ N₃ : Type*}
    [CommSemiring R] [AddCommMonoid A] [Module R A] [Coalgebra R A]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P]
    [AddCommMonoid M'] [Module R M'] [AddCommMonoid N'] [Module R N']
    [AddCommMonoid P'] [Module R P'] [AddCommMonoid Q] [Module R Q] [AddCommMonoid Q'] [Module R Q']
    [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
    [AddCommMonoid N₁] [AddCommMonoid N₂] [AddCommMonoid N₃]
    [Module R M₁] [Module R M₂] [Module R M₃] [Module R N₁] [Module R N₂] [Module R N₃]

local notation3 "α" => (TensorProduct.assoc R _ _ _).toLinearMap

local notation3 "α⁻¹" => (TensorProduct.assoc R _ _ _).symm.toLinearMap

local notation3 "λ" => (TensorProduct.lid R _).toLinearMap

local notation3 "λ⁻¹" => (TensorProduct.lid R _).symm.toLinearMap

local notation3 "ρ" => (TensorProduct.rid R _).toLinearMap

local notation3 "ρ⁻¹" => (TensorProduct.rid R _).symm.toLinearMap

local notation3 "β" => (TensorProduct.comm R _ _).toLinearMap

local infix:90 " ⊗ₘ " => TensorProduct.map

local notation3 "δ" => comul (R := R)

local notation3 "ε" => counit (R := R)

attribute [coassoc_simps] LinearMap.comp_id LinearMap.id_comp TensorProduct.map_id

  LinearMap.lTensor_def LinearMap.rTensor_def LinearMap.comp_assoc
  LinearEquiv.coe_trans LinearEquiv.trans_symm
  LinearEquiv.refl_toLinearMap TensorProduct.toLinearMap_congr
  LinearEquiv.comp_symm LinearEquiv.symm_comp LinearEquiv.symm_symm
  LinearEquiv.coe_lTensor LinearEquiv.coe_lTensor_symm
  LinearEquiv.coe_rTensor LinearEquiv.coe_rTensor_symm
  IsCocomm.comm_comp_comul TensorProduct.AlgebraTensorModule.map_eq
  TensorProduct.AlgebraTensorModule.assoc_eq TensorProduct.AlgebraTensorModule.rightComm_eq
  TensorProduct.tensorTensorTensorComm TensorProduct.AlgebraTensorModule.tensorTensorTensorComm
  TensorProduct.AlgebraTensorModule.congr_eq LinearEquiv.comp_symm_assoc
  LinearEquiv.symm_comp_assoc TensorProduct.rightComm_def TensorProduct.leftComm_def
  TensorProduct.comm_symm TensorProduct.comm_comp_comm TensorProduct.comm_comp_comm_assoc

attribute [coassoc_simps← ] TensorProduct.map_comp TensorProduct.map_map_comp_assoc_eq

  TensorProduct.map_map_comp_assoc_symm_eq
