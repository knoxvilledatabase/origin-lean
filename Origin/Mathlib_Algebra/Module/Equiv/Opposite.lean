/-
Extracted from Algebra/Module/Equiv/Opposite.lean
Genuine: 2 | Conflates: 0 | Dissolved: 0 | Infrastructure: 8
-/
import Origin.Core
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Algebra.Module.Opposite

noncomputable section

/-!
# Module operations on `Mᵐᵒᵖ`

This file contains definitions that build on top of the group action definitions in
`Mathlib.Algebra.GroupWithZero.Action.Opposite`.
-/

section

variable {R S M : Type*} [Semiring R] [Semiring S] [AddCommMonoid M] [Module S M]

@[ext high]
theorem LinearMap.ext_ring_op
    {σ : Rᵐᵒᵖ →+* S} {f g : R →ₛₗ[σ] M} (h : f (1 : R) = g (1 : R)) :
    f = g :=
  ext fun x ↦ by
    -- Porting note: replaced the oneliner `rw` proof with a partially term-mode proof
    -- because `rw` was giving "motive is type incorrect" errors
    rw [← one_mul x, ← op_smul_eq_mul]
    refine (f.map_smulₛₗ (MulOpposite.op x) 1).trans ?_
    rw [h]
    exact (g.map_smulₛₗ (MulOpposite.op x) 1).symm

end

namespace MulOpposite

universe u v

variable (R : Type u) {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]

def opLinearEquiv : M ≃ₗ[R] Mᵐᵒᵖ :=
  { opAddEquiv with map_smul' := MulOpposite.op_smul }

end MulOpposite
