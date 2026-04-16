/-
Extracted from Tactic/NthRewrite.lean
Genuine: 1 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Init
import Lean.Elab.Tactic.Rewrite

noncomputable section

/-!
# `nth_rewrite` tactic

The tactic `nth_rewrite` and `nth_rw` are variants of `rewrite` and `rw` that only performs the
`n`th possible rewrite.

-/

namespace Mathlib.Tactic

open Lean Elab Tactic Meta Parser.Tactic

syntax (name := nthRewriteSeq) "nth_rewrite" optConfig ppSpace num+ rwRuleSeq (location)? : tactic

@[inherit_doc nthRewriteSeq, tactic nthRewriteSeq] def evalNthRewriteSeq : Tactic := fun stx => do
  match stx with
  | `(tactic| nth_rewrite $cfg:optConfig $[$n]* $_rules:rwRuleSeq $[$loc]?) =>
    let cfg ← elabRewriteConfig cfg
    let loc := expandOptLocation (mkOptionalNode loc)
    let occ := Occurrences.pos (n.map TSyntax.getNat).toList
    let cfg := { cfg with occs := occ }
    withRWRulesSeq stx[0] stx[3] fun symm term => do
      withLocation loc
        (rewriteLocalDecl term symm · cfg)
        (rewriteTarget term symm cfg)
        (throwTacticEx `nth_rewrite · "did not find instance of the pattern in the current goal")
  | _ => throwUnsupportedSyntax

macro (name := nthRwSeq) "nth_rw" c:optConfig ppSpace n:num+ s:rwRuleSeq l:(location)? : tactic =>
  -- Note: This is a direct copy of `nth_rw` from core.
  match s with
  | `(rwRuleSeq| [$rs,*]%$rbrak) =>
    -- We show the `rfl` state on `]`
    `(tactic| (nth_rewrite $c:optConfig $[$n]* [$rs,*] $(l)?; with_annotate_state $rbrak
      (try (with_reducible rfl))))
  | _ => Macro.throwUnsupported

end Mathlib.Tactic
