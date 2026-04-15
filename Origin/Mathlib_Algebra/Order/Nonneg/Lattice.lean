/-
Extracted from Algebra/Order/Nonneg/Lattice.lean
Genuine: 2 of 9 | Dissolved: 0 | Infrastructure: 7
-/
import Origin.Core

/-!
# Lattice structures on the type of nonnegative elements

-/

assert_not_exists Ring

assert_not_exists IsOrderedMonoid

open Set

variable {α : Type*}

namespace Nonneg

-- INSTANCE (free from Core): orderBot

-- INSTANCE (free from Core): noMaxOrder

-- INSTANCE (free from Core): semilatticeSup

-- INSTANCE (free from Core): semilatticeInf

-- INSTANCE (free from Core): distribLattice

-- INSTANCE (free from Core): instDenselyOrdered

protected noncomputable abbrev conditionallyCompleteLinearOrder [ConditionallyCompleteLinearOrder α]
    {a : α} : ConditionallyCompleteLinearOrder { x : α // a ≤ x } :=
  -- TODO: missing `Inhabited (Ici a)` instance
  haveI : Inhabited (Ici a) := ⟨a, le_rfl⟩
  inferInstanceAs <| ConditionallyCompleteLinearOrder (Ici a)

set_option backward.isDefEq.respectTransparency false in

protected noncomputable abbrev conditionallyCompleteLinearOrderBot
    [ConditionallyCompleteLinearOrder α] (a : α) :
    ConditionallyCompleteLinearOrderBot { x : α // a ≤ x } :=
  { Nonneg.orderBot, Nonneg.conditionallyCompleteLinearOrder with
    csSup_empty := by
      rw [@subset_sSup_def α (Set.Ici a) _ _ ⟨⟨a, le_rfl⟩⟩]; simp [bot_eq] }

end Nonneg
