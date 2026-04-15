/-
Extracted from Data/Tree/Get.lean
Genuine: 3 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Data.Num.Basic
import Mathlib.Data.Ordering.Basic
import Mathlib.Data.Tree.Basic

/-!
# Binary tree get operation

In this file we define `Tree.indexOf`, `Tree.get`, and `Tree.getOrElse`.
These definitions were moved from the main file to avoid a dependency on `Num`.

## References

<https://leanprover-community.github.io/archive/stream/113488-general/topic/tactic.20question.html#170999997>
-/

namespace Tree

variable {α : Type*}

def indexOf (lt : α → α → Prop) [DecidableRel lt] (x : α) : Tree α → Option PosNum
  | nil => none
  | node a t₁ t₂ =>
    match cmpUsing lt x a with
    | Ordering.lt => PosNum.bit0 <$> indexOf lt x t₁
    | Ordering.eq => some PosNum.one
    | Ordering.gt => PosNum.bit1 <$> indexOf lt x t₂

def get : PosNum → Tree α → Option α
  | _, nil => none
  | PosNum.one, node a _t₁ _t₂ => some a
  | PosNum.bit0 n, node _a t₁ _t₂ => t₁.get n
  | PosNum.bit1 n, node _a _t₁ t₂ => t₂.get n

def getOrElse (n : PosNum) (t : Tree α) (v : α) : α :=
  (t.get n).getD v

end Tree
