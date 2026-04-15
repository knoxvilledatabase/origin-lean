/-
Extracted from Tactic/MoveAdd.lean
Genuine: 16 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Algebra.Group.Basic
import Mathlib.Lean.Meta

/-!

#  `move_add` a tactic for moving summands in expressions

The tactic `move_add` rearranges summands in expressions.

The tactic takes as input a list of terms, each one optionally preceded by `←`.
A term preceded by `←` gets moved to the left, while a term without `←` gets moved to the right.

* Empty input: `move_add []`

  In this case, the effect of `move_add []` is equivalent to `simp only [← add_assoc]`:
  essentially the tactic removes all visible parentheses.

* Singleton input: `move_add [a]` and `move_add [← a]`

  If `⊢ b + a + c` is (a summand in) the goal, then
  * `move_add [← a]` changes the goal to `a + b + c` (effectively, `a` moved to the left).
  * `move_add [a]` changes the goal to `b + c + a` (effectively, `a` moved to the right);

  The tactic reorders *all* sub-expressions of the target at the same same.
  For instance, if `⊢ 0 < if b + a < b + a + c then a + b else b + a` is the goal, then
  * `move_add [a]` changes the goal to `0 < if b + a < b + c + a then b + a else b + a`
    (`a` moved to the right in three sums);
  * `move_add [← a]` changes the goal to `0 < if a + b < a + b + c then a + b else a + b`
    (`a` again moved to the left in three sums).

* Longer inputs: `move_add [..., a, ..., ← b, ...]`

  If the list contains more than one term, the tactic effectively tries to move each term preceded
  by `←` to the left, each term not preceded by `←` to the right
  *maintaining the relative order in the call*.
  Thus, applying `move_add [a, b, c, ← d, ← e]` returns summands of the form
  `d + e + [...] + a + b + c`, i.e. `d` and `e` have the same relative position in the input list
  and in the final rearrangement (and similarly for `a, b, c`).
  In particular, `move_add [a, b]` likely has the same effect as
  `move_add [a]; move_add [b]`: first, we move `a` to the right, then we move `b` also to the
  right, *after* `a`.
  However, if the terms matched by `a` and `b` do not overlap, then `move_add [← a, ← b]`
  has the same effect as `move_add [b]; move_add [a]`:
  first, we move `b` to the left, then we move `a` also to the left, *before* `a`.
  The behaviour in the situation where `a` and `b` overlap is unspecified: `move_add`
  will descend into subexpressions, but the order in which they are visited depends
  on which rearrangements have already happened.
  Also note, though, that `move_add [a, b]` may differ `move_add [a]; move_add [b]`,
  for instance when `a` and `b` are `DefEq`.

* Unification of inputs and repetitions: `move_add [_, ← _, a * _]`

  The matching of the user inputs with the atoms of the summands in the target expression
  is performed via checking `DefEq` and selecting the first, still available match.
  Thus, if a sum in the target is `2 * 3 + 4 * (5 + 6) + 4 * 7 + 10 * 10`, then
  `move_add [4 * _]` moves the summand `4 * (5 + 6)` to the right.

  The unification of later terms only uses the atoms in the target that have not yet been unified.
  Thus, if again the target contains `2 * 3 + 4 * (5 + 6) + 4 * 7 + 10 * 10`, then
  `move_add [_, ← _, 4 * _]`
  matches
  * the first input (`_`) with `2 * 3`;
  * the second input (`_`) with `4 * (5 + 6)`;
  * the third input (`4 * _`) with `4 * 7`.

  The resulting permutation therefore places `2 * 3` and `4 * 7` to the left (in this order) and
  `4 * (5 + 6)` to the right: `2 * 3 + 4 * 7 + 10 * 10 + 4 * (5 + 6)`.

For the technical description, look at `Mathlib.MoveAdd.weight` and `Mathlib.MoveAdd.reorderUsing`.

`move_add` is the specialization of a more general `move_oper` tactic that takes a binary,
associative, commutative operation and a list of "operand atoms" and rearranges the operation.

## Extension notes

To work with a general associative, commutative binary operation, `move_oper`
needs to have inbuilt the lemmas asserting the analogues of
`add_comm, add_assoc, add_left_comm` for the new operation.
Currently, `move_oper` supports `HAdd.hAdd`, `HMul.hMul`, `And`, `Or`, `Max.max`, `Min.min`.

These lemmas should be added to `Mathlib.MoveAdd.move_oper_simpCtx`.

See `test/MoveAdd.lean` for sample usage of `move_oper`.

## Implementation notes

The main driver behind the tactic is `Mathlib.MoveAdd.reorderAndSimp`.

The tactic takes the target, replaces the maximal subexpressions whose head symbol is the given
operation and replaces them by their reordered versions.
Once that is done, it tries to replace the initial goal with the permuted one by using `simp`.

Currently, no attempt is made at guiding `simp` by doing a `congr`-like destruction of the goal.
This will be the content of a later PR.
-/

open Lean Expr

def Lean.Expr.getExprInputs : Expr → Array Expr
  | app fn arg        => #[fn, arg]
  | lam _ bt bb _     => #[bt, bb]
  | forallE _ bt bb _ => #[bt, bb]
  | letE _ t v b _    => #[t, v, b]
  | mdata _ e         => #[e]
  | proj _ _ e        => #[e]
  | _ => #[]

partial

def Lean.Expr.size (e : Expr) : ℕ := (e.getExprInputs.map size).foldl (· + ·) 1

namespace Mathlib.MoveAdd

section ExprProcessing

section reorder

variable {α : Type*} [BEq α]

/-!
##  Reordering the variables

This section produces the permutations of the variables for `move_add`.

The user controls the final order by passing a list of terms to the tactic.
Each term can be preceded by `←` or not.
In the final ordering,
* terms preceded by `←` appear first,
* terms not preceded by `←` appear last,
* all remaining terms remain in their current relative order.
-/

def uniquify : List α → List (α × ℕ)
  | []    => []
  | m::ms =>
    let lms := uniquify ms
    (m, 0) :: (lms.map fun (x, n) => if x == m then (x, n + 1) else (x, n))

def weight (L : List (α × Bool)) (a : α) : ℤ :=
  let l := L.length
  match L.find? (Prod.fst · == a) with
    | some (_, b) => if b then - l + (L.indexOf (a, b) : ℤ) else (L.indexOf (a, b) + 1 : ℤ)
    | none => 0

def reorderUsing (toReorder : List α) (instructions : List (α × Bool)) : List α :=
  let uInstructions :=
    let (as, as?) := instructions.unzip
    (uniquify as).zip as?
  let uToReorder := (uniquify toReorder).toArray
  let reorder := uToReorder.qsort fun x y =>
    match uInstructions.find? (Prod.fst · == x), uInstructions.find? (Prod.fst · == y) with
      | none, none => (uToReorder.getIdx? x).get! ≤ (uToReorder.getIdx? y).get!
      | _, _ => weight uInstructions x ≤ weight uInstructions y
  (reorder.map Prod.fst).toList

end reorder

def prepareOp (sum : Expr) : Expr :=
  let opargs := sum.getAppArgs
  (opargs.toList.take (opargs.size - 2)).foldl (fun x y => Expr.app x y) sum.getAppFn

partial

def sumList (prepOp : Expr) (left_assoc? : Bool) : List Expr → Expr
  | []    => default
  | [a]   => a
  | a::as =>
    if left_assoc? then
      Expr.app (prepOp.app a) (sumList prepOp true as)
    else
      as.foldl (fun x y => Expr.app (prepOp.app x) y) a

end ExprProcessing

open Meta

variable (op : Name)

variable (R : Expr) in

partial def getAddends (sum : Expr) : MetaM (Array Expr) := do
  if sum.isAppOf op then
    let inR ← sum.getAppArgs.filterM fun r => do isDefEq R (← inferType r <|> pure R)
    let new ← inR.mapM (getAddends ·)
    return new.foldl Array.append  #[]
  else return #[sum]

partial def getOps (sum : Expr) : MetaM (Array ((Array Expr) × Expr)) := do
  let summands ← getAddends op (← inferType sum <|> return sum) sum
  let (first, rest) := if summands.size == 1 then (#[], sum.getExprInputs) else
    (#[(summands, sum)], summands)
  let rest ← rest.mapM getOps
  return rest.foldl Array.append first

def rankSums (tgt : Expr) (instructions : List (Expr × Bool)) : MetaM (List (Expr × Expr)) := do
  let sums ← getOps op (← instantiateMVars tgt)
  let candidates := sums.map fun (addends, sum) => do
    let reord := reorderUsing addends.toList instructions
    let left_assoc? := sum.getAppFn.isConstOf `And || sum.getAppFn.isConstOf `Or
    let resummed := sumList (prepareOp sum) left_assoc? reord
    if (resummed != sum) then some (sum, resummed) else none
  return (candidates.toList.reduceOption.toArray.qsort
    (fun x y : Expr × Expr ↦ (y.1.size  ≤ x.1.size))).toList

def permuteExpr (tgt : Expr) (instructions : List (Expr × Bool)) : MetaM Expr := do
  let permInstructions ← rankSums op tgt instructions
  if permInstructions == [] then throwError "The goal is already in the required form"
  let mut permTgt := tgt
  -- We cannot do `Expr.replace` all at once here, we need to follow
  -- the order of the instructions.
  for (old, new) in permInstructions do
    permTgt := permTgt.replace (if · == old then new else none)
  return permTgt

```

-/

def pairUp : List (Expr × Bool × Syntax) → List Expr →
    MetaM ((List (Expr × Bool)) × List (Expr × Bool × Syntax))
  | (m::ms), l => do
    match ← l.findM? (isDefEq · m.1) with
      | none => let (found, unfound) ← pairUp ms l; return (found, m::unfound)
      | some d => let (found, unfound) ← pairUp ms (l.erase d)
                  return ((d, m.2.1)::found, unfound)
  | _, _ => return ([], [])

def move_oper_simpCtx : MetaM Simp.Context := do
  let simpNames := Elab.Tactic.simpOnlyBuiltins ++ [
    ``add_comm, ``add_assoc, ``add_left_comm,  -- for `HAdd.hAdd`
    ``mul_comm, ``mul_assoc, ``mul_left_comm,  -- for `HMul.hMul`
    ``and_comm, ``and_assoc, ``and_left_comm,  -- for `and`
    ``or_comm,  ``or_assoc,  ``or_left_comm,   -- for `or`
    ``max_comm, ``max_assoc, ``max_left_comm,  -- for `max`
    ``min_comm, ``min_assoc, ``min_left_comm   -- for `min`
    ]
  let simpThms ← simpNames.foldlM (·.addConst ·) ({} : SimpTheorems)
  return { simpTheorems := #[simpThms] }

def reorderAndSimp (mv : MVarId) (instr : List (Expr × Bool)) :
    MetaM (List MVarId) := mv.withContext do
  let permExpr ← permuteExpr op (← mv.getType'') instr
  -- generate the implication `permutedMv → mv = permutedMv → mv`
  let eqmpr ← mkAppM ``Eq.mpr #[← mkFreshExprMVar (← mkEq (← mv.getType) permExpr)]
  let twoGoals ← mv.apply eqmpr
  guard (twoGoals.length == 2) <|>
    throwError m!"There should only be 2 goals, instead of {twoGoals.length}"
  -- `permGoal` is the single goal `mv_permuted`, possibly more operations will be permuted later on
  let permGoal ← twoGoals.filterM fun v => return !(← v.isAssigned)
  match ← (simpGoal (permGoal[1]!) (← move_oper_simpCtx)) with
    | (some x, _) => throwError m!"'move_oper' could not solve {indentD x.2}"
    | (none, _) => return permGoal

def unifyMovements (data : Array (Expr × Bool × Syntax)) (tgt : Expr) :
    MetaM (List (Expr × Bool) × (List MessageData × List Syntax) × Array MessageData) := do
  let ops ← getOps op tgt
  let atoms := (ops.map Prod.fst).flatten.toList.filter (!isBVar ·)
  -- `instr` are the unified user-provided terms, `neverMatched` are non-unified ones
  let (instr, neverMatched) ← pairUp data.toList atoms
  let dbgMsg := #[m!"Matching of input variables:\n\
    * pre-match:  {data.map (Prod.snd ∘ Prod.snd)}\n\
    * post-match: {instr}",
    m!"\nMaximum number of iterations: {ops.size}"]
  -- if there are `neverMatched` terms, return the parsed terms and the syntax
  let errMsg := neverMatched.map fun (t, a, stx) => (if a then m!"← {t}" else m!"{t}", stx)
  return (instr, errMsg.unzip, dbgMsg)

section parsing

open Elab Parser Tactic

def parseArrows : TSyntax `Lean.Parser.Tactic.rwRuleSeq → TermElabM (Array (Expr × Bool × Syntax))
  | `(rwRuleSeq| [$rs,*]) => do
    rs.getElems.mapM fun rstx => do
      let r : Syntax := rstx
      return (← Term.elabTerm r[1]! none, ! r[0]!.isNone, rstx)
  | _ => failure

initialize registerTraceClass `Tactic.move_oper

elab (name := moveOperTac) "move_oper" id:ident rws:rwRuleSeq : tactic => withMainContext do

  let op := id.getId

  let (instr, (unmatched, stxs), dbgMsg) ← unifyMovements op (← parseArrows rws)

                                                              (← instantiateMVars (← getMainTarget))

  unless unmatched.length = 0 do

    let _ ← stxs.mapM (logErrorAt · "") -- underline all non-matching terms

    trace[Tactic.move_oper] dbgMsg.foldl (fun x y => (x.compose y).compose "\n\n---\n") ""

    throwErrorAt stxs[0]! m!"Errors:\nThe terms in '{unmatched}' were not matched to any atom"

  replaceMainGoal (← reorderAndSimp op (← getMainGoal) instr)

elab "move_add" rws:rwRuleSeq : tactic => do

  let hadd := mkIdent ``HAdd.hAdd

  evalTactic (← `(tactic| move_oper $hadd $rws))

elab "move_mul" rws:rwRuleSeq : tactic => do

  let hmul := mkIdent ``HMul.hMul

  evalTactic (← `(tactic| move_oper $hmul $rws))

end parsing

end MoveAdd

end Mathlib
