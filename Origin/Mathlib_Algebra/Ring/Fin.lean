/-
Extracted from Algebra/Ring/Fin.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Rings and `Fin`

This file collects some basic results involving rings and the `Fin` type

## Main results

 * `RingEquiv.piFinTwo`: The product over `Fin 2` of some rings is the cartesian product

-/

@[simps]
def RingEquiv.piFinTwo (R : Fin 2 → Type*) [∀ i, Semiring (R i)] :
    (∀ i : Fin 2, R i) ≃+* R 0 × R 1 :=
  { piFinTwoEquiv R with
    toFun := piFinTwoEquiv R
    map_add' := fun _ _ => rfl
    map_mul' := fun _ _ => rfl }
