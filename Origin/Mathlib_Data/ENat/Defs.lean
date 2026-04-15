/-
Extracted from Data/ENat/Defs.lean
Genuine: 2 | Conflates: 0 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core
import Mathlib.Data.Nat.Notation
import Mathlib.Order.TypeTags

/-! # Definition and notation for extended natural numbers -/

def ENat : Type := WithTop ℕ deriving Top, Inhabited

namespace ENat

instance instNatCast : NatCast ℕ∞ := ⟨WithTop.some⟩

@[elab_as_elim, induction_eliminator, cases_eliminator]
def recTopCoe {C : ℕ∞ → Sort*} (top : C ⊤) (coe : ∀ a : ℕ, C a) : ∀ n : ℕ∞, C n
  | none => top
  | Option.some a => coe a

@[simp]
theorem recTopCoe_top {C : ℕ∞ → Sort*} (d : C ⊤) (f : ∀ a : ℕ, C a) :
    @recTopCoe C d f ⊤ = d :=
  rfl

@[simp]
theorem recTopCoe_coe {C : ℕ∞ → Sort*} (d : C ⊤) (f : ∀ a : ℕ, C a) (x : ℕ) :
    @recTopCoe C d f ↑x = f x :=
  rfl

end ENat
