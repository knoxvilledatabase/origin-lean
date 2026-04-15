/-
Extracted from Algebra/Order/Module/Basic.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Further lemmas about monotonicity of scalar multiplication
-/

variable {𝕜 R M : Type*}

section Semiring

variable [Semiring R] [Invertible (2 : R)] [Lattice M] [AddCommGroup M] [Module R M]
  [IsOrderedAddMonoid M]

variable (R) in

lemma inf_eq_half_smul_add_sub_abs_sub (x y : M) : x ⊓ y = (⅟2 : R) • (x + y - |y - x|) := by
  rw [← two_nsmul_inf_eq_add_sub_abs_sub x y, two_smul, ← two_smul R,
    smul_smul, invOf_mul_self, one_smul]

variable (R) in

lemma sup_eq_half_smul_add_add_abs_sub (x y : M) : x ⊔ y = (⅟2 : R) • (x + y + |y - x|) := by
  rw [← two_nsmul_sup_eq_add_add_abs_sub x y, two_smul, ← two_smul R,
    smul_smul, invOf_mul_self, one_smul]

end Semiring

section Ring

variable [Ring R] [LinearOrder R] [IsOrderedRing R] [AddCommGroup M] [LinearOrder M]
  [IsOrderedAddMonoid M] [Module R M] [PosSMulMono R M]
