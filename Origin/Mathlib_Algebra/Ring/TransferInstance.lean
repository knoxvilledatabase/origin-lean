/-
Extracted from Algebra/Ring/TransferInstance.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Transfer algebraic structures across `Equiv`s

This continues the pattern set in `Mathlib/Algebra/Group/TransferInstance.lean`.
-/

assert_not_exists Field Module

namespace Equiv

variable {α β : Type*} (e : α ≃ β)

def ringEquiv (e : α ≃ β) [Add β] [Mul β] : by
    let add := Equiv.add e
    let mul := Equiv.mul e
    exact α ≃+* β := by
  intros
  exact
    { e with
      map_add' := fun x y => by
        simp [add_def]
      map_mul' := fun x y => by
        simp [mul_def] }
