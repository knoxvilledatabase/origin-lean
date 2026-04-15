/-
Extracted from Algebra/Ring/AddAut.lean
Genuine: 2 of 4 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.Algebra.GroupWithZero.Action.Basic
import Mathlib.Algebra.GroupWithZero.Action.Units
import Mathlib.Algebra.Group.Units.Opposite
import Mathlib.Algebra.Module.Opposite

/-!
# Multiplication on the left/right as additive automorphisms

In this file we define `AddAut.mulLeft` and `AddAut.mulRight`.

See also `AddMonoidHom.mulLeft`, `AddMonoidHom.mulRight`, `AddMonoid.End.mulLeft`, and
`AddMonoid.End.mulRight` for multiplication by `R` as an endomorphism instead of multiplication by
`Rˣ` as an automorphism.
-/

namespace AddAut

variable {R : Type*} [Semiring R]

@[simps! (config := { simpRhs := true })]
def mulLeft : Rˣ →* AddAut R :=
  DistribMulAction.toAddAut _ _

def mulRight (u : Rˣ) : AddAut R :=
  DistribMulAction.toAddAut Rᵐᵒᵖˣ R (Units.opEquiv.symm <| MulOpposite.op u)

@[simp]
theorem mulRight_apply (u : Rˣ) (x : R) : mulRight u x = x * u :=
  rfl

@[simp]
theorem mulRight_symm_apply (u : Rˣ) (x : R) : (mulRight u).symm x = x * u⁻¹ :=
  rfl

end AddAut
