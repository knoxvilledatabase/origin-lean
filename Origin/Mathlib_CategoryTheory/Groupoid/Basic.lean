/-
Extracted from CategoryTheory/Groupoid/Basic.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
This file defines a few basic properties of groupoids.
-/

namespace CategoryTheory

namespace Groupoid

variable (C : Type*) [Groupoid C]

section Thin

end Thin

section Disconnected

def IsTotallyDisconnected :=
  ∀ c d : C, (c ⟶ d) → c = d

end Disconnected

end Groupoid

end CategoryTheory
