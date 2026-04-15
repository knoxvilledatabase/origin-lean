/-
Extracted from Logic/Equiv/Finset.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# `Encodable` and `Denumerable` instances for `Finset`
-/

variable {α}

open Encodable

-- INSTANCE (free from Core): Finset.encodable

namespace Encodable

def sortedUniv (α) [Fintype α] [Encodable α] : List α :=
  Finset.univ.sort (Encodable.encode' α ⁻¹'o (· ≤ ·))
