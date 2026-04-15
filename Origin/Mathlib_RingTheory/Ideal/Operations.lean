/-
Extracted from RingTheory/Ideal/Operations.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# More operations on modules and ideals
-/

assert_not_exists Module.Basis -- See `RingTheory.Ideal.Basis`

  Submodule.hasQuotient -- See `RingTheory.Ideal.Quotient.Operations`

universe u v w x

open Module

open scoped Pointwise

namespace Submodule

lemma coe_span_smul {R' M' : Type*} [CommSemiring R'] [AddCommMonoid M'] [Module R' M']
    (s : Set R') (N : Submodule R' M') :
    (Ideal.span s : Set R') • N = s • N :=
  set_smul_eq_of_le _ _ _
    (by rintro r n hr hn
        induction hr using Submodule.span_induction with
        | mem _ h => exact mem_set_smul_of_mem_mem h hn
        | zero => rw [zero_smul]; exact Submodule.zero_mem _
        | add _ _ _ _ ihr ihs => rw [add_smul]; exact Submodule.add_mem _ ihr ihs
        | smul _ _ hr =>
          rw [mem_span_set] at hr
          obtain ⟨c, hc, rfl⟩ := hr
          rw [Finsupp.sum, Finset.smul_sum, Finset.sum_smul]
          refine Submodule.sum_mem _ fun i hi => ?_
          rw [← mul_smul, smul_eq_mul, mul_comm, mul_smul]
          exact mem_set_smul_of_mem_mem (hc hi) <| Submodule.smul_mem _ _ hn) <|
    set_smul_mono_left _ Submodule.subset_span

lemma span_singleton_toAddSubgroup_eq_zmultiples (a : ℤ) :
    (span ℤ {a}).toAddSubgroup = AddSubgroup.zmultiples a := by
  ext i
  simp [Ideal.mem_span_singleton', AddSubgroup.mem_zmultiples_iff]
