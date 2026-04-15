/-
Extracted from Lean/Expr/ReplaceRec.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Lean.Expr
import Mathlib.Util.MemoFix

/-!
# ReplaceRec

We define a more flexible version of `Expr.replace` where we can use recursive calls even when
replacing a subexpression. We completely mimic the implementation of `Expr.replace`.
-/

namespace Lean.Expr

def replaceRec (f? : (Expr → Expr) → Expr → Option Expr) : Expr → Expr :=
  memoFix fun r e ↦
    match f? r e with
    | some x => x
    | none   => traverseChildren (M := Id) r e

end Lean.Expr
