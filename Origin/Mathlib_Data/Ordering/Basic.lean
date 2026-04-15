/-
Extracted from Data/Ordering/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Helper definitions and instances for `Ordering`
-/

universe u

namespace Ordering

variable {α : Type*}

def Compares [LT α] : Ordering → α → α → Prop
  | lt, a, b => a < b
  | eq, a, b => a = b
  | gt, a, b => a > b
