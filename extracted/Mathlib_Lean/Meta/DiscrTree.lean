/-
Extracted from Lean/Meta/DiscrTree.lean
Genuine: 2 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Init
import Lean.Meta.DiscrTree

noncomputable section

/-!
# Additions to `Lean.Meta.DiscrTree`
-/

namespace Lean.Meta.DiscrTree

partial def getSubexpressionMatches {α : Type}
    (d : DiscrTree α) (e : Expr) (config : WhnfCoreConfig) : MetaM (Array α) := do
  match e with
  | .bvar _ => return #[]
  | .forallE _ _ _ _ => forallTelescope e (fun args body => do
      args.foldlM (fun acc arg => do
          pure <| acc ++ (← d.getSubexpressionMatches (← inferType arg) config))
        (← d.getSubexpressionMatches body config).reverse)
  | .lam _ _ _ _
  | .letE _ _ _ _ _ => lambdaLetTelescope e (fun args body => do
      args.foldlM (fun acc arg => do
          pure <| acc ++ (← d.getSubexpressionMatches (← inferType arg) config))
        (← d.getSubexpressionMatches body config).reverse)
  | _ =>
    e.foldlM (fun a f => do
      pure <| a ++ (← d.getSubexpressionMatches f config)) (← d.getMatch e config).reverse

def keysSpecific (keys : Array DiscrTree.Key) : Bool :=
  keys != #[Key.star] && keys != #[Key.const ``Eq 3, Key.star, Key.star, Key.star]

end Lean.Meta.DiscrTree
