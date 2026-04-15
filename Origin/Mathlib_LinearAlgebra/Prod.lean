/-
Extracted from LinearAlgebra/Prod.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! ### Products of modules

This file defines constructors for linear maps whose domains or codomains are products.

It contains theorems relating these to each other, as well as to `Submodule.prod`, `Submodule.map`,
`Submodule.comap`, `LinearMap.range`, and `LinearMap.ker`.

## Main definitions

- products in the domain:
  - `LinearMap.fst`
  - `LinearMap.snd`
  - `LinearMap.coprod`
  - `LinearMap.prod_ext`
- products in the codomain:
  - `LinearMap.inl`
  - `LinearMap.inr`
  - `LinearMap.prod`
- products in both domain and codomain:
  - `LinearMap.prodMap`
  - `LinearEquiv.prodMap`
  - `LinearEquiv.skewProd`
- product with the trivial module:
  - `LinearEquiv.prodUnique`
  - `LinearEquiv.uniqueProd`
-/

universe u v w x y z u' v' w' y'

variable {R : Type u} {K : Type u'} {M : Type v} {V : Type v'} {M₂ : Type w} {V₂ : Type w'}

variable {M₃ : Type y} {V₃ : Type y'} {M₄ : Type z} {ι : Type x}

variable {M₅ M₆ : Type*}

section Prod

namespace LinearMap

variable (S : Type*) [Semiring R] [Semiring S]

variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃] [AddCommMonoid M₄]

variable [AddCommMonoid M₅] [AddCommMonoid M₆]

variable [Module R M] [Module R M₂] [Module R M₃] [Module R M₄]

variable [Module R M₅] [Module R M₆]

variable (f : M →ₗ[R] M₂)

variable (R M M₂)

def fst : M × M₂ →ₗ[R] M where
  toFun := Prod.fst
  map_add' _x _y := rfl
  map_smul' _x _y := rfl

def snd : M × M₂ →ₗ[R] M₂ where
  toFun := Prod.snd
  map_add' _x _y := rfl
  map_smul' _x _y := rfl

end
