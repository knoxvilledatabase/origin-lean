/-
Extracted from Util/Qq.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Init
import Qq

/-!
# Extra `Qq` helpers

This file contains some additional functions for using the quote4 library more conveniently.
-/

open Lean Elab Tactic Meta

namespace Qq

def inferTypeQ' (e : Expr) : MetaM ((u : Level) × (α : Q(Type $u)) × Q($α)) := do
  let α ← inferType e
  let .sort u ← whnf (← inferType α) | throwError "not a type{indentExpr α}"
  let some v := (← instantiateLevelMVars u).dec | throwError "not a Type{indentExpr e}"
  pure ⟨v, α, e⟩

theorem QuotedDefEq.rfl {u : Level} {α : Q(Sort u)} {a : Q($α)} : @QuotedDefEq u α a a := ⟨⟩

end Qq
