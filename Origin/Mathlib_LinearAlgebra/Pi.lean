/-
Extracted from LinearAlgebra/Pi.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Pi types of modules

This file defines constructors for linear maps whose domains or codomains are pi types.

It contains theorems relating these to each other, as well as to `LinearMap.ker`.

## Main definitions

- pi types in the codomain:
  - `LinearMap.pi`
  - `LinearMap.single`
- pi types in the domain:
  - `LinearMap.proj`
  - `LinearMap.diag`

-/

universe u v w x y z u' v' w' x' y'

variable {R : Type u} {K : Type u'} {M : Type v} {V : Type v'} {M₂ : Type w} {V₂ : Type w'}

variable {M₃ : Type y} {V₃ : Type y'} {M₄ : Type z} {ι : Type x} {ι' : Type x'}

open Function Submodule

namespace LinearMap

universe i

variable [Semiring R] [AddCommMonoid M₂] [Module R M₂] [AddCommMonoid M₃] [Module R M₃]
  {φ : ι → Type i} [(i : ι) → AddCommMonoid (φ i)] [(i : ι) → Module R (φ i)]

def pi (f : (i : ι) → M₂ →ₗ[R] φ i) : M₂ →ₗ[R] (i : ι) → φ i :=
  { Pi.addHom fun i => (f i).toAddHom with
    toFun := fun c i => f i c
    map_smul' := fun _ _ => funext fun i => (f i).map_smul _ _ }
