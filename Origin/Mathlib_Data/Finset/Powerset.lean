/-
Extracted from Data/Finset/Powerset.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The powerset of a finset
-/

namespace Finset

open Function Multiset

variable {α : Type*} {s t : Finset α}

/-! ### powerset -/

section Powerset

def powerset (s : Finset α) : Finset (Finset α) :=
  ⟨(s.1.powerset.pmap Finset.mk) fun _t h => nodup_of_le (mem_powerset.1 h) s.nodup,
    s.nodup.powerset.pmap fun _a _ha _b _hb => congr_arg Finset.val⟩
