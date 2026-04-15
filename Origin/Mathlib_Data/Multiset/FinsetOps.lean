/-
Extracted from Data/Multiset/FinsetOps.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Preparations for defining operations on `Finset`.

The operations here ignore multiplicities,
and prepare for defining the corresponding operations on `Finset`.
-/

assert_not_exists Set.sInter

namespace Multiset

open List

variable {α : Type*} [DecidableEq α] {s : Multiset α}

/-! ### finset insert -/

def ndinsert (a : α) (s : Multiset α) : Multiset α :=
  Quot.liftOn s (fun l => (l.insert a : Multiset α)) fun _ _ p => Quot.sound (p.insert a)
