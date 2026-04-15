/-
Extracted from RingTheory/DualNumber.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Algebraic properties of dual numbers

## Main results

* `DualNumber.instLocalRing`: The dual numbers over a field `K` form a local ring.
* `DualNumber.instPrincipalIdealRing`: The dual numbers over a field `K` form a principal ideal
  ring.

-/

namespace TrivSqZeroExt

variable {R M : Type*}

section Semiring

variable [Semiring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M]

lemma isNilpotent_iff_isNilpotent_fst {x : TrivSqZeroExt R M} :
    IsNilpotent x ↔ IsNilpotent x.fst := by
  constructor <;> rintro ⟨n, hn⟩
  · refine ⟨n, ?_⟩
    rw [← fst_pow, hn, fst_zero]
  · refine ⟨n * 2, ?_⟩
    rw [pow_mul]
    ext
    · rw [fst_pow, fst_pow, hn, zero_pow two_ne_zero, fst_zero]
    · rw [pow_two, snd_mul, fst_pow, hn, MulOpposite.op_zero, zero_smul, zero_smul, zero_add,
        snd_zero]
