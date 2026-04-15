/-
Extracted from Algebra/Ring/Action/Group.lean
Genuine: 1 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Algebra.GroupWithZero.Action.Basic
import Mathlib.Algebra.Ring.Action.Basic
import Mathlib.Algebra.Ring.Equiv

/-!
# If a group acts multiplicatively on a semiring, each group element acts by a ring automorphism.

This result is split out from `Mathlib.Algebra.Ring.Action.Basic`
to avoid needing the import of `Mathlib.Algebra.GroupWithZero.Action.Basic`.
-/

section Semiring

variable (G : Type*) [Group G]

variable (R : Type*) [Semiring R]

@[simps!]
def MulSemiringAction.toRingEquiv [MulSemiringAction G R] (x : G) : R ≃+* R :=
  { DistribMulAction.toAddEquiv R x, MulSemiringAction.toRingHom G R x with }

end Semiring
