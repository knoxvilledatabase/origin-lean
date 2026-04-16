/-
Extracted from Data/Int/DivMod.lean
Genuine: 2 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Init

noncomputable section

/-!
# Basic lemmas about division and modulo for integers

-/

namespace Int

/-! ### `emod` -/

theorem emod_eq_sub_self_emod {a b : Int} : a % b = (a - b) % b :=
  (emod_sub_cancel a b).symm

theorem emod_eq_add_self_emod {a b : Int} : a % b = (a + b) % b :=
  add_emod_self.symm

end Int
