/-
Extracted from Data/Finset/Attach.lean
Genuine: 2 | Conflates: 0 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core
import Mathlib.Data.Finset.Defs

noncomputable section

/-!
# Attaching a proof of membership to a finite set

## Main declarations

* `Finset.attach`: Given `s : Finset α`, `attach s` forms a finset of elements of the subtype
  `{a // a ∈ s}`; in other words, it attaches elements to a proof of membership in the set.

## Tags

finite sets, finset

-/

open Multiset Subtype Function

universe u

variable {α : Type*} {β : Type*} {γ : Type*}

namespace Finset

attribute [local trans] Subset.trans Superset.trans

/-! ### attach -/

def attach (s : Finset α) : Finset { x // x ∈ s } :=
  ⟨Multiset.attach s.1, nodup_attach.2 s.2⟩

@[simp]
theorem attach_val (s : Finset α) : s.attach.1 = s.1.attach :=
  rfl

@[simp]
theorem mem_attach (s : Finset α) : ∀ x, x ∈ s.attach :=
  Multiset.mem_attach _

end Finset
