/-
Extracted from Data/Fintype/Prod.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# fintype instance for the product of two fintypes.

-/

open Function

universe u v

variable {α β γ : Type*}

open Finset

namespace Set

variable {s t : Set α}

theorem toFinset_prod (s : Set α) (t : Set β) [Fintype s] [Fintype t] [Fintype (s ×ˢ t)] :
    (s ×ˢ t).toFinset = s.toFinset ×ˢ t.toFinset := by
  ext
  simp

theorem toFinset_offDiag {s : Set α} [Fintype s] [Fintype s.offDiag] :
    s.offDiag.toFinset = s.toFinset.offDiag :=
  Finset.ext <| by simp
