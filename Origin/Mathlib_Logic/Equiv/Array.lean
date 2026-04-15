/-
Extracted from Logic/Equiv/Array.lean
Genuine: 1 | Conflates: 0 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.Data.Vector.Basic
import Mathlib.Logic.Equiv.List

/-!
# Equivalences involving `Array`
-/

namespace Equiv

def arrayEquivList (α : Type*) : Array α ≃ List α :=
  ⟨Array.toList, Array.mk, fun _ => rfl, fun _ => rfl⟩

end Equiv

instance Array.encodable {α} [Encodable α] : Encodable (Array α) :=
  Encodable.ofEquiv _ (Equiv.arrayEquivList _)

instance Array.countable {α} [Countable α] : Countable (Array α) :=
  Countable.of_equiv _ (Equiv.arrayEquivList α).symm
