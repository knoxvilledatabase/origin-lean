/-
Extracted from Lean/Expr/Rat.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Init
import Batteries.Data.Rat.Basic
import Batteries.Tactic.Alias

/-!
# Additional operations on Expr and rational numbers

This file defines some operations involving `Expr` and rational numbers.

## Main definitions

 * `Lean.Expr.isExplicitNumber`: is an expression a number in normal form?
   This includes natural numbers, integers and rationals.
-/

namespace Lean.Expr

def rat? (e : Expr) : Option Rat := do
  if e.isAppOfArity ``Div.div 4 then
    let d ← e.appArg!.nat?
    guard (d ≠ 1)
    let n ← e.appFn!.appArg!.int?
    let q := mkRat n d
    guard (q.den = d)
    pure q
  else
    e.int?

def isExplicitNumber : Expr → Bool
  | .lit _ => true
  | .mdata _ e => isExplicitNumber e
  | e => e.rat?.isSome

end Lean.Expr
