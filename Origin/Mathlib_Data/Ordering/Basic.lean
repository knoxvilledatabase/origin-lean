/-
Extracted from Data/Ordering/Basic.lean
Genuine: 3 of 7 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core
import Batteries.Tactic.Alias
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar

/-!
# Helper definitions and instances for `Ordering`
-/

universe u

deriving instance Repr for Ordering

namespace Ordering

variable {α : Type*}

def Compares [LT α] : Ordering → α → α → Prop
  | lt, a, b => a < b
  | eq, a, b => a = b
  | gt, a, b => a > b

@[simp] lemma compares_lt [LT α] (a b : α) : Compares lt a b = (a < b) := rfl

@[simp] lemma compares_eq [LT α] (a b : α) : Compares eq a b = (a = b) := rfl

@[simp] lemma compares_gt [LT α] (a b : α) : Compares gt a b = (a > b) := rfl

end Ordering

def cmpUsing {α : Type u} (lt : α → α → Prop) [DecidableRel lt] (a b : α) : Ordering :=
  if lt a b then Ordering.lt else if lt b a then Ordering.gt else Ordering.eq

def cmp {α : Type u} [LT α] [DecidableRel ((· < ·) : α → α → Prop)] (a b : α) : Ordering :=
  cmpUsing (· < ·) a b
