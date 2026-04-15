/-
Extracted from Algebra/Module/NatInt.lean
Genuine: 1 of 9 | Dissolved: 0 | Infrastructure: 8
-/
import Origin.Core

/-!
# Modules over `ℕ` and `ℤ`

This file concerns modules where the scalars are the natural numbers or the integers.

## Main definitions

* `AddCommMonoid.toNatModule`: any `AddCommMonoid` is (uniquely) a module over the naturals.
* `AddCommGroup.toIntModule`: any `AddCommGroup` is a module over the integers.

## Main results

* `AddCommMonoid.uniqueNatModule`: there is a unique `AddCommMonoid ℕ M` structure for any `M`

## Tags

semimodule, module, vector space
-/

assert_not_exists RelIso Field Invertible Multiset Pi.single_smul₀ Set.indicator

open Function Set

universe u v

variable {R S M M₂ : Type*}

-- INSTANCE (free from Core): [AddMonoid

-- INSTANCE (free from Core): [AddMonoid

-- INSTANCE (free from Core): [SubtractionMonoid

-- INSTANCE (free from Core): [SubtractionMonoid

section AddCommMonoid

variable [AddCommMonoid M]

-- INSTANCE (free from Core): AddCommMonoid.toNatModule

end AddCommMonoid

section AddCommGroup

variable (M) [AddCommGroup M]

-- INSTANCE (free from Core): AddCommGroup.toIntModule

end AddCommGroup

variable (R) in

abbrev Module.addCommMonoidToAddCommGroup
    [Ring R] [AddCommMonoid M] [Module R M] : AddCommGroup M :=
  { (inferInstance : AddCommMonoid M) with
    neg := fun a => (-1 : R) • a
    neg_add_cancel := fun a =>
      show (-1 : R) • a + a = 0 by
        nth_rw 2 [← one_smul R a]
        rw [← add_smul, neg_add_cancel, zero_smul]
    zsmul := fun z a => (z : R) • a
    zsmul_zero' := fun a => by simpa only [Int.cast_zero] using zero_smul R a
    zsmul_succ' := fun z a => by simp [add_comm, add_smul]
    zsmul_neg' := fun z a => by simp [← smul_assoc] }

section AddCommMonoid

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable (R)
