/-
Extracted from Lean/Elab/Term.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Init
import Lean.Elab.SyntheticMVars

/-!
# Additions to `Lean.Elab.Term`
-/

namespace Lean.Elab.Term

def elabPattern (patt : Term) (expectedType? : Option Expr) : TermElabM Expr := do
  withTheReader Term.Context ({ · with ignoreTCFailures := true, errToSorry := false }) <|
    withSynthesizeLight do
      let t ← elabTerm patt expectedType?
      synthesizeSyntheticMVars (postpone := .no) (ignoreStuckTC := true)
      instantiateMVars t

end Lean.Elab.Term
