/-
Extracted from Logic/Equiv/Array.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Equivalences involving `Array`
-/

namespace Equiv

def arrayEquivList (α : Type*) : Array α ≃ List α where
  toFun := Array.toList
  invFun := Array.mk

end Equiv

-- INSTANCE (free from Core): Array.encodable

-- INSTANCE (free from Core): Array.countable
