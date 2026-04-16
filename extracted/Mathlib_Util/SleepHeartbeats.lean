/-
Extracted from Util/SleepHeartbeats.lean
Genuine: 1 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Init
import Lean.Elab.Tactic.Basic

noncomputable section

/-!
# Defines `sleep_heartbeats` tactic.

This is useful for testing / debugging long running commands or elaboration in a somewhat precise
manner.
-/

open Lean Elab

def sleepAtLeastHeartbeats (n : Nat) : IO Unit := do
  let i ← IO.getNumHeartbeats
  while (← IO.getNumHeartbeats) < i + n do
    continue

elab "sleep_heartbeats " n:num : tactic => do
  match Syntax.isNatLit? n with
  | none    => throwIllFormedSyntax
  /- as this is a user facing command we multiply the user input by 1000 to match the maxHeartbeats
     option -/
  | some m => sleepAtLeastHeartbeats (m * 1000)

example : 1 = 1 := by
  sleep_heartbeats 1000
  rfl
