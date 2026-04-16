/-
Extracted from Data/PNat/Equiv.lean
Genuine: 1 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Data.PNat.Defs
import Mathlib.Logic.Equiv.Defs

noncomputable section

/-!
# The equivalence between `ℕ+` and `ℕ`
-/

@[simps (config := .asFn)]
def _root_.Equiv.pnatEquivNat : ℕ+ ≃ ℕ where
  toFun := PNat.natPred
  invFun := Nat.succPNat
  left_inv := PNat.succPNat_natPred
  right_inv := Nat.natPred_succPNat
