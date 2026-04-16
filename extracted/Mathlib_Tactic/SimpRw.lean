/-
Extracted from Tactic/SimpRw.lean
Genuine: 1 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Init

noncomputable section

/-!
# The `simp_rw` tactic

This file defines the `simp_rw` tactic: it functions as a mix of `simp` and `rw`.
Like `rw`, it applies each rewrite rule in the given order, but like `simp` it repeatedly applies
these rules and also under binders like `∀ x, ...`, `∃ x, ...` and `fun x ↦ ...`.
-/

namespace Mathlib.Tactic

open Lean Elab.Tactic

open Parser.Tactic (optConfig rwRuleSeq location getConfigItems)

def withSimpRWRulesSeq (token : Syntax) (rwRulesSeqStx : Syntax)
    (x : (symm : Bool) → (term : Syntax) → TacticM Unit) : TacticM Unit := do
  let lbrak := rwRulesSeqStx[0]
  let rules := rwRulesSeqStx[1].getArgs
  -- show initial state up to (incl.) `[`
  withTacticInfoContext (mkNullNode #[token, lbrak]) (pure ())
  let numRules := (rules.size + 1) / 2
  for i in [:numRules] do
    let rule := rules[i * 2]!
    let sep  := rules.getD (i * 2 + 1) Syntax.missing
    -- show rule state up to (incl.) next `,`
    withTacticInfoContext (mkNullNode #[rule, sep]) do
      -- show errors on rule
      withRef rule do
        let symm := !rule[0].isNone
        let term := rule[1]
        -- let processId (id : Syntax) : TacticM Unit := do
        x symm term

elab s:"simp_rw " cfg:optConfig rws:rwRuleSeq g:(location)? : tactic => focus do
  evalTactic (← `(tactic| simp%$s $[$(getConfigItems cfg)]* (failIfUnchanged := false) only $(g)?))
  withSimpRWRulesSeq s rws fun symm term => do
    evalTactic (← match term with
    | `(term| $e:term) =>
      if symm then
        `(tactic| simp%$e $cfg only [← $e:term] $g ?)
      else
        `(tactic| simp%$e $cfg only [$e:term] $g ?))

end Mathlib.Tactic
