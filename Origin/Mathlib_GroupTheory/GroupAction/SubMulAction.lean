/-
Extracted from GroupTheory/GroupAction/SubMulAction.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Sets invariant to a `MulAction`

In this file we define `SubMulAction R M`; a subset of a `MulAction R M` which is closed with
respect to scalar multiplication.

For most uses, typically `Submodule R M` is more powerful.

## Main definitions

* `SubMulAction.mulAction` - the `MulAction R M` transferred to the subtype.
* `SubMulAction.mulAction'` - the `MulAction S M` transferred to the subtype when
  `IsScalarTower S R M`.
* `SubMulAction.isScalarTower` - the `IsScalarTower S R M` transferred to the subtype.
* `SubMulAction.inclusion` — the inclusion of a `SubMulAction`, as an equivariant map

## Tags

submodule, multiplicative action
-/

open Function

universe u u' u'' v

variable {S : Type u'} {T : Type u''} {R : Type u} {M : Type v}

class SMulMemClass (S : Type*) (R : outParam Type*) (M : Type*) [SMul R M] [SetLike S M] :
    Prop where
  /-- Multiplication by a scalar on an element of the set remains in the set. -/
  smul_mem : ∀ {s : S} (r : R) {m : M}, m ∈ s → r • m ∈ s

class VAddMemClass (S : Type*) (R : outParam Type*) (M : Type*) [VAdd R M] [SetLike S M] :
    Prop where
  /-- Addition by a scalar with an element of the set remains in the set. -/
  vadd_mem : ∀ {s : S} (r : R) {m : M}, m ∈ s → r +ᵥ m ∈ s

attribute [to_additive] SMulMemClass

attribute [aesop 90% (rule_sets := [SetLike])] SMulMemClass.smul_mem VAddMemClass.vadd_mem

lemma AddSubmonoidClass.nsmulMemClass {S M : Type*} [AddMonoid M] [SetLike S M]
    [AddSubmonoidClass S M] : SMulMemClass S ℕ M where
  smul_mem n _x hx := nsmul_mem hx n

lemma AddSubgroupClass.zsmulMemClass {S M : Type*} [SubNegMonoid M] [SetLike S M]
    [AddSubgroupClass S M] : SMulMemClass S ℤ M where
  smul_mem n _x hx := zsmul_mem hx n

namespace SetLike

open SMulMemClass

section SMul

variable [SMul R M] [SetLike S M] [hS : SMulMemClass S R M] (s : S)
