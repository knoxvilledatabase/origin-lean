/-
Extracted from Tactic/FinCases.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Tactic.Core
import Mathlib.Lean.Expr.Basic
import Mathlib.Data.Fintype.Basic

/-!
# The `fin_cases` tactic.

Given a hypothesis of the form `h : x ∈ (A : List α)`, `x ∈ (A : Finset α)`,
or `x ∈ (A : Multiset α)`,
or a hypothesis of the form `h : A`, where `[Fintype A]` is available,
`fin_cases h` will repeatedly call `cases` to split the goal into
separate cases for each possible value.
-/

open Lean.Meta

namespace Lean.Elab.Tactic

def getMemType {m : Type → Type} [Monad m] [MonadError m] (e : Expr) : m (Option Expr) := do
  match e.getAppFnArgs with
  | (``Membership.mem, #[_, type, _, _, _]) =>
    match type.getAppFnArgs with
    | (``List, #[α])     => return α
    | (``Multiset, #[α]) => return α
    | (``Finset, #[α])   => return α
    | _ => throwError "Hypothesis must be of type `x ∈ (A : List α)`, `x ∈ (A : Finset α)`, \
                       or `x ∈ (A : Multiset α)`"
  | _ => return none

partial def unfoldCases (g : MVarId) (h : FVarId)
    (userNamePre : Name := .anonymous) (counter := 0) : MetaM (List MVarId) := do
  let gs ← g.cases h
  try
    let #[g₁, g₂] := gs | throwError "unexpected number of cases"
    g₁.mvarId.setUserName (.str userNamePre s!"{counter}")
    let gs ← unfoldCases g₂.mvarId g₂.fields[2]!.fvarId! userNamePre (counter+1)
    return g₁.mvarId :: gs
  catch _ => return []

partial def finCasesAt (g : MVarId) (hyp : FVarId) : MetaM (List MVarId) := g.withContext do
  let type ← hyp.getType >>= instantiateMVars
  match ← getMemType type with
  | some _ => unfoldCases g hyp (userNamePre := ← g.getTag)
  | none =>
    -- Deal with `x : A`, where `[Fintype A]` is available:
    let inst ← synthInstance (← mkAppM ``Fintype #[type])
    let elems ← mkAppOptM ``Fintype.elems #[type, inst]
    let t ← mkAppM ``Membership.mem #[elems, .fvar hyp]
    let v ← mkAppOptM ``Fintype.complete #[type, inst, Expr.fvar hyp]
    let (fvar, g) ← (← g.assert `this t v).intro1P
    finCasesAt g fvar

syntax (name := finCases) "fin_cases " ("*" <|> term,+) (" with " term,+)? : tactic

/-!
`fin_cases` used to also have two modifiers, `fin_cases ... with ...` and `fin_cases ... using ...`.
With neither actually used in mathlib, they haven't been re-implemented here.

In case someone finds a need for them, and wants to re-implement, the relevant sections of
the doc-string are preserved here:

---

`fin_cases h with l` takes a list of descriptions for the cases of `h`.
These should be definitionally equal to and in the same order as the
default enumeration of the cases.

For example,
```
example (x y : ℕ) (h : x ∈ [1, 2]) : x = y := by
  fin_cases h with 1, 1+1
```
produces two cases: `1 = y` and `1 + 1 = y`.

When using `fin_cases a` on data `a` defined with `let`,
the tactic will not be able to clear the variable `a`,
and will instead produce hypotheses `this : a = ...`.
These hypotheses can be given a name using `fin_cases a using ha`.

For example,
```
example (f : ℕ → Fin 3) : True := by
  let a := f 3
  fin_cases a using ha
```
produces three goals with hypotheses
`ha : a = 0`, `ha : a = 1`, and `ha : a = 2`.
-/

  | `(tactic| fin_cases $[$hyps:ident],*) => withMainContext <| focus do

    for h in hyps do

      allGoals <| liftMetaTactic (finCasesAt · (← getFVarId h))

end Tactic

end Elab

end Lean
