/-
Extracted from Algebra/GradedMulAction.lean
Genuine: 3 of 9 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core

/-!
# Additively-graded multiplicative action structures

This module provides a set of heterogeneous typeclasses for defining a multiplicative structure
over the sigma type `GradedMonoid A` such that `(•) : A i → M j → M (i +ᵥ j)`; that is to say, `A`
has an additively-graded multiplicative action on `M`. The typeclasses are:

* `GradedMonoid.GSMul A M`
* `GradedMonoid.GMulAction A M`

With the `SigmaGraded` scope open, these respectively imbue:

* `SMul (GradedMonoid A) (GradedMonoid M)`
* `MulAction (GradedMonoid A) (GradedMonoid M)`

For now, these typeclasses are primarily used in the construction of `DirectSum.GModule.Module` and
the rest of that file.

## Internally graded multiplicative actions

In addition to the above typeclasses, in the most frequent case when `A` is an indexed collection of
`SetLike` subobjects (such as `AddSubmonoid`s, `AddSubgroup`s, or `Submodule`s), this file
provides the `Prop` typeclasses:

* `SetLike.GradedSMul A M` (which provides the obvious `GradedMonoid.GSMul A` instance)

which provides the API lemma

* `SetLike.graded_smul_mem_graded`

Note that there is no need for `SetLike.graded_mul_action` or similar, as all the information it
would contain is already supplied by `GradedSMul` when the objects within `A` and `M` have
a `MulAction` instance.

## Tags

graded action
-/

variable {ιA ιB ιM : Type*}

namespace GradedMonoid

/-! ### Typeclasses -/

section Defs

variable (A : ιA → Type*) (M : ιM → Type*)

class GSMul [VAdd ιA ιM] where
  /-- The homogeneous multiplication map `smul` -/
  smul {i j} : A i → M j → M (i +ᵥ j)

-- INSTANCE (free from Core): GMul.toGSMul

-- INSTANCE (free from Core): GSMul.toSMul

class GMulAction [AddMonoid ιA] [VAdd ιA ιM] [GMonoid A] extends GSMul A M where
  /-- One is the neutral element for `•` -/
  one_smul (b : GradedMonoid M) : (1 : GradedMonoid A) • b = b
  /-- Associativity of `•` and `*` -/
  mul_smul (a a' : GradedMonoid A) (b : GradedMonoid M) : (a * a') • b = a • a' • b

-- INSTANCE (free from Core): GMonoid.toGMulAction

-- INSTANCE (free from Core): GMulAction.toMulAction

end Defs

end GradedMonoid

/-! ### Shorthands for creating instance of the above typeclasses for collections of subobjects -/

section Subobjects

variable {R : Type*}

class SetLike.GradedSMul {S R N M : Type*} [SetLike S R] [SetLike N M] [SMul R M] [VAdd ιA ιB]
  (A : ιA → S) (B : ιB → N) : Prop where
  /-- Multiplication is homogeneous -/
  smul_mem : ∀ ⦃i : ιA⦄ ⦃j : ιB⦄ {ai bj}, ai ∈ A i → bj ∈ B j → ai • bj ∈ B (i +ᵥ j)

-- INSTANCE (free from Core): SetLike.toGSMul
