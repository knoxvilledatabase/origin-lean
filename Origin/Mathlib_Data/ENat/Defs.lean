/-
Extracted from Data/ENat/Defs.lean
Genuine: 2 | Conflates: 0 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core
import Mathlib.Data.Nat.Notation
import Mathlib.Order.TypeTags

noncomputable section

/-! # Definition and notation for extended natural numbers -/

def ENat : Type := WithTop ℕ deriving Top, Inhabited

@[inherit_doc] notation "ℕ∞" => ENat

namespace ENat

instance instNatCast : NatCast ℕ∞ := ⟨WithTop.some⟩

@[elab_as_elim, induction_eliminator, cases_eliminator]
def recTopCoe {C : ℕ∞ → Sort*} (top : C ⊤) (coe : ∀ a : ℕ, C a) : ∀ n : ℕ∞, C n
  | none => top
  | Option.some a => coe a

end ENat
