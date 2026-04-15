/-
Extracted from Algebra/Module/Submodule/LinearMap.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Linear maps involving submodules of a module

In this file we define a number of linear maps involving submodules of a module.

## Main declarations

* `Submodule.subtype`: Embedding of a submodule `p` to the ambient space `M` as a `Submodule`.
* `LinearMap.domRestrict`: The restriction of a semilinear map `f : M → M₂` to a submodule `p ⊆ M`
  as a semilinear map `p → M₂`.
* `LinearMap.restrict`: The restriction of a linear map `f : M → M₁` to a submodule `p ⊆ M` and
  `q ⊆ M₁` (if `q` contains the codomain).
* `Submodule.inclusion`: the inclusion `p ⊆ p'` of submodules `p` and `p'` as a linear map.

## Tags

submodule, subspace, linear map
-/

open Function Set

universe u'' u' u v w

variable {G : Type u''} {S : Type u'} {R : Type u} {M : Type v} {ι : Type w}

namespace SMulMemClass

variable [Semiring R] [AddCommMonoid M] [Module R M] {A : Type*} [SetLike A M]
  [AddSubmonoidClass A M] [SMulMemClass A R M] (S' : A)

protected def subtype : S' →ₗ[R] M where
  toFun := Subtype.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {S'} in
