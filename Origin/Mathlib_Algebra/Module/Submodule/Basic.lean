/-
Extracted from Algebra/Module/Submodule/Basic.lean
Genuine: 11 of 21 | Dissolved: 2 | Infrastructure: 8
-/
import Origin.Core
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.NoZeroSMulDivisors.Defs
import Mathlib.GroupTheory.GroupAction.SubMulAction

/-!
# Submodules of a module

This file contains basic results on submodules that require further theory to be defined.
As such it is a good target for organizing and splitting further.

## Tags

submodule, subspace, linear map
-/

open Function

universe u'' u' u v w

variable {G : Type u''} {S : Type u'} {R : Type u} {M : Type v} {ι : Type w}

namespace Submodule

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable {p q : Submodule R M}

@[mono]
theorem toAddSubmonoid_strictMono : StrictMono (toAddSubmonoid : Submodule R M → AddSubmonoid M) :=
  fun _ _ => id

theorem toAddSubmonoid_le : p.toAddSubmonoid ≤ q.toAddSubmonoid ↔ p ≤ q :=
  Iff.rfl

@[mono]
theorem toAddSubmonoid_mono : Monotone (toAddSubmonoid : Submodule R M → AddSubmonoid M) :=
  toAddSubmonoid_strictMono.monotone

@[mono]
theorem toSubMulAction_strictMono :
    StrictMono (toSubMulAction : Submodule R M → SubMulAction R M) := fun _ _ => id

@[mono]
theorem toSubMulAction_mono : Monotone (toSubMulAction : Submodule R M → SubMulAction R M) :=
  toSubMulAction_strictMono.monotone

end Submodule

namespace Submodule

section AddCommMonoid

variable [Semiring R] [AddCommMonoid M]

variable {module_M : Module R M}

variable {p q : Submodule R M}

variable {r : R} {x y : M}

variable (p)

protected theorem sum_mem {t : Finset ι} {f : ι → M} : (∀ c ∈ t, f c ∈ p) → (∑ i ∈ t, f i) ∈ p :=
  sum_mem

theorem sum_smul_mem {t : Finset ι} {f : ι → M} (r : ι → R) (hyp : ∀ c ∈ t, f c ∈ p) :
    (∑ i ∈ t, r i • f i) ∈ p :=
  sum_mem fun i hi => smul_mem _ _ (hyp i hi)

instance isCentralScalar [SMul S R] [SMul S M] [IsScalarTower S R M] [SMul Sᵐᵒᵖ R] [SMul Sᵐᵒᵖ M]
    [IsScalarTower Sᵐᵒᵖ R M] [IsCentralScalar S M] : IsCentralScalar S p :=
  p.toSubMulAction.isCentralScalar

instance noZeroSMulDivisors [NoZeroSMulDivisors R M] : NoZeroSMulDivisors R p :=
  ⟨fun {c} {x : p} h =>
    have : c = 0 ∨ (x : M) = 0 := eq_zero_or_eq_zero_of_smul_eq_zero (congr_arg Subtype.val h)
    this.imp_right (@Subtype.ext_iff _ _ x 0).mpr⟩

section AddAction

/-! ### Additive actions by `Submodule`s
These instances transfer the action by an element `m : M` of an `R`-module `M` written as `m +ᵥ a`
onto the action by an element `s : S` of a submodule `S : Submodule R M` such that
`s +ᵥ a = (s : M) +ᵥ a`.
These instances work particularly well in conjunction with `AddGroup.toAddAction`, enabling
`s +ᵥ m` as an alias for `↑s + m`.
-/

variable {α β : Type*}

instance [VAdd M α] : VAdd p α :=
  p.toAddSubmonoid.vadd

instance vaddCommClass [VAdd M β] [VAdd α β] [VAddCommClass M α β] : VAddCommClass p α β :=
  ⟨fun a => (vadd_comm (a : M) : _)⟩

instance [VAdd M α] [FaithfulVAdd M α] : FaithfulVAdd p α :=
  ⟨fun h => Subtype.ext <| eq_of_vadd_eq_vadd h⟩

variable {p}

theorem vadd_def [VAdd M α] (g : p) (m : α) : g +ᵥ m = (g : M) +ᵥ m :=
  rfl

end AddAction

end AddCommMonoid

section AddCommGroup

variable [Ring R] [AddCommGroup M]

variable {module_M : Module R M}

variable (p p' : Submodule R M)

variable {r : R} {x y : M}

@[mono]
theorem toAddSubgroup_strictMono : StrictMono (toAddSubgroup : Submodule R M → AddSubgroup M) :=
  fun _ _ => id

theorem toAddSubgroup_le : p.toAddSubgroup ≤ p'.toAddSubgroup ↔ p ≤ p' :=
  Iff.rfl

@[mono]
theorem toAddSubgroup_mono : Monotone (toAddSubgroup : Submodule R M → AddSubgroup M) :=
  toAddSubgroup_strictMono.monotone

theorem neg_coe : -(p : Set M) = p :=
  Set.ext fun _ => p.neg_mem_iff

end AddCommGroup

section IsDomain

variable [Ring R] [IsDomain R]

variable [AddCommGroup M] [Module R M] {b : ι → M}

theorem not_mem_of_ortho {x : M} {N : Submodule R M}
    (ortho : ∀ (c : R), ∀ y ∈ N, c • x + y = (0 : M) → c = 0) : x ∉ N := by
  intro hx
  simpa using ortho (-1) x hx

-- DISSOLVED: ne_zero_of_ortho

end IsDomain

end Submodule

namespace Submodule

variable [DivisionSemiring S] [Semiring R] [AddCommMonoid M] [Module R M]

variable [SMul S R] [Module S M] [IsScalarTower S R M]

variable (p : Submodule R M) {s : S} {x y : M}

-- DISSOLVED: smul_mem_iff

end Submodule

abbrev Subspace (R : Type u) (M : Type v) [DivisionRing R] [AddCommGroup M] [Module R M] :=
  Submodule R M
