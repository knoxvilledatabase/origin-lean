/-
Extracted from Data/Multiset/Dedup.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Erasing duplicates in a multiset.
-/

assert_not_exists Monoid

namespace Multiset

open List

variable {α β : Type*} [DecidableEq α]

/-! ### dedup -/

def dedup (s : Multiset α) : Multiset α :=
  Quot.liftOn s (fun l => (l.dedup : Multiset α)) fun _ _ p => Quot.sound p.dedup
