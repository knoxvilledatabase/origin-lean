/-
Extracted from LinearAlgebra/TensorProduct/Quotient.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Interaction between Quotients and Tensor Products

This file contains constructions that relate quotients and tensor products. This file is also a home
for results whose proof depends on both tensor products and linear algebraic quotients.
Let `M, N` be `R`-modules, `m ≤ M` and `n ≤ N` be an `R`-submodules and `I ≤ R` an ideal. We prove
the following isomorphisms:

## Main results
- `TensorProduct.quotientTensorQuotientEquiv`:
  `(M ⧸ m) ⊗[R] (N ⧸ n) ≃ₗ[R] (M ⊗[R] N) ⧸ (m ⊗ N ⊔ M ⊗ n)`
- `TensorProduct.quotientTensorEquiv`:
  `(M ⧸ m) ⊗[R] N ≃ₗ[R] (M ⊗[R] N) ⧸ (m ⊗ N)`
- `TensorProduct.tensorQuotientEquiv`:
  `M ⊗[R] (N ⧸ n) ≃ₗ[R] (M ⊗[R] N) ⧸ (M ⊗ n)`
- `TensorProduct.quotTensorEquivQuotSMul`:
  `(R ⧸ I) ⊗[R] M ≃ₗ[R] M ⧸ (I • M)`
- `TensorProduct.tensorQuotEquivQuotSMul`:
  `M ⊗[R] (R ⧸ I) ≃ₗ[R] M ⧸ (I • M)`

## Tags

Quotient, Tensor Product

-/

assert_not_exists Cardinal

namespace TensorProduct

variable {R M N : Type*} [CommRing R]

variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

attribute [local ext high] ext LinearMap.prod_ext

noncomputable def quotientTensorQuotientEquiv (m : Submodule R M) (n : Submodule R N) :
    (M ⧸ (m : Submodule R M)) ⊗[R] (N ⧸ (n : Submodule R N)) ≃ₗ[R]
    (M ⊗[R] N) ⧸
      (LinearMap.range (map m.subtype LinearMap.id) ⊔
        LinearMap.range (map LinearMap.id n.subtype)) :=
  LinearEquiv.ofLinear
    (lift <| Submodule.liftQ _ (LinearMap.flip <| Submodule.liftQ _
      ((mk R (M := M) (N := N)).flip.compr₂ (Submodule.mkQ _)) fun x hx => by
      ext y
      simp only [LinearMap.compr₂_apply, LinearMap.flip_apply, mk_apply, Submodule.mkQ_apply,
        LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero]
      exact Submodule.mem_sup_right ⟨y ⊗ₜ ⟨x, hx⟩, rfl⟩) fun x hx => by
      ext y
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, LinearMap.flip_apply,
        Submodule.liftQ_apply, LinearMap.compr₂_apply, mk_apply, LinearMap.zero_comp,
        LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero]
      exact Submodule.mem_sup_left ⟨⟨x, hx⟩ ⊗ₜ y, rfl⟩)
    (Submodule.liftQ _ (map (Submodule.mkQ _) (Submodule.mkQ _)) fun x hx => by
      rw [Submodule.mem_sup] at hx
      rcases hx with ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩
      simp only [LinearMap.mem_ker, map_add]
      set f := (map m.mkQ n.mkQ) ∘ₗ (map m.subtype LinearMap.id)
      set g := (map m.mkQ n.mkQ) ∘ₗ (map LinearMap.id n.subtype)
      have eq : LinearMap.coprod f g = 0 := by
        ext x y
        · simp [f, Submodule.Quotient.mk_eq_zero _ |>.2 x.2]
        · simp [g, Submodule.Quotient.mk_eq_zero _ |>.2 y.2]
      exact congr($eq (a, b)))
    (by ext; simp) (by ext; simp)
