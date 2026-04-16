/-
Extracted from LinearAlgebra/Finsupp/SumProd.lean
Genuine: 2 | Conflates: 0 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Prod
import Mathlib.Data.Finsupp.Basic

noncomputable section

/-!
# Finsupps and sum/product types

This file contains results about modules involving `Finsupp` and sum/product/sigma types.

## Tags

function with finite support, module, linear algebra
-/

noncomputable section

open Set LinearMap

namespace Finsupp

variable {α : Type*} {M : Type*} {N : Type*} {P : Type*} {R : Type*} {S : Type*}

variable [Semiring R] [Semiring S] [AddCommMonoid M] [Module R M]

variable [AddCommMonoid N] [Module R N]

variable [AddCommMonoid P] [Module R P]

section Sum

variable (R)

@[simps apply symm_apply]
def sumFinsuppLEquivProdFinsupp {α β : Type*} : (α ⊕ β →₀ M) ≃ₗ[R] (α →₀ M) × (β →₀ M) :=
  { sumFinsuppAddEquivProdFinsupp with
    map_smul' := by
      intros
      ext <;>
        -- Porting note: `add_equiv.to_fun_eq_coe` →
        --               `Equiv.toFun_as_coe` & `AddEquiv.toEquiv_eq_coe` & `AddEquiv.coe_toEquiv`
        simp only [Equiv.toFun_as_coe, AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv, Prod.smul_fst,
          Prod.smul_snd, smul_apply,
          snd_sumFinsuppAddEquivProdFinsupp, fst_sumFinsuppAddEquivProdFinsupp,
          RingHom.id_apply] }

end Sum

section Sigma

variable {η : Type*} [Fintype η] {ιs : η → Type*} [Zero α]

variable (R)

noncomputable def sigmaFinsuppLEquivPiFinsupp {M : Type*} {ιs : η → Type*} [AddCommMonoid M]
    [Module R M] : ((Σ j, ιs j) →₀ M) ≃ₗ[R] (j : _) → (ιs j →₀ M) :=
  -- Porting note: `ιs` should be specified.
  { sigmaFinsuppAddEquivPiFinsupp (ιs := ιs) with
    map_smul' := fun c f => by
      ext
      simp }

end Sigma

end Finsupp
