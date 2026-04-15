/-
Extracted from CategoryTheory/FinCategory/AsType.lean
Genuine: 3 of 4 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Finite categories are equivalent to categories in `Type 0`.
-/

universe w v u

noncomputable section

namespace CategoryTheory

namespace FinCategory

variable (α : Type*) [Fintype α] [SmallCategory α] [FinCategory α]

abbrev ObjAsType : Type :=
  InducedCategory α (Fintype.equivFin α).symm

-- INSTANCE (free from Core): {i

noncomputable def objAsTypeEquiv : ObjAsType α ≌ α :=
  (inducedFunctor (Fintype.equivFin α).symm).asEquivalence

abbrev AsType : Type :=
  Fin (Fintype.card α)
