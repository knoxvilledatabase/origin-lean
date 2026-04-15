/-
Extracted from Lean/Exception.lean
Genuine: 2 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Init
import Lean.Exception

/-!
# Additional methods for working with `Exception`s

This file contains two additional methods for working with `Exception`s
* `successIfFail`, a generalisation of `fail_if_success` to arbitrary `MonadError`s
* `isFailedToSynthesize`: check if an exception is of the "failed to synthesize" form

-/

open Lean

def successIfFail {α : Type} {M : Type → Type} [MonadError M] [Monad M] (m : M α) :
    M Exception := do
  match ← tryCatch (m *> pure none) (pure ∘ some) with
  | none => throwError "Expected an exception."
  | some ex => return ex

namespace Lean

namespace Exception

def isFailedToSynthesize (e : Exception) : IO Bool := do
  pure <| (← e.toMessageData.toString).startsWith "failed to synthesize"

end Exception

end Lean
