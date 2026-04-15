/-
Extracted from Data/MLList/Dedup.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Init
import Batteries.Data.MLList.Basic
import Batteries.Data.HashMap.Basic

/-!
# Lazy deduplication of lazy lists

## Deprecation

This material has been moved out of Mathlib to https://github.com/semorrison/lean-monadic-list.
-/

set_option linter.deprecated false

open Batteries

namespace MLList

variable {α β : Type} {m : Type → Type} [Monad m] [BEq β] [Hashable β]

def dedupBy (L : MLList m α) (f : α → m β) : MLList m α :=
  ((L.liftM : MLList (StateT (HashMap β Unit) m) α) >>= fun a => do
      let b ← f a
      guard !(← get).contains b
      modify fun s => s.insert b ()
      pure a)
  |>.runState' ∅

def dedup (L : MLList m β) : MLList m β := L.dedupBy pure

end MLList
