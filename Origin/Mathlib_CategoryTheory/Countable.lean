/-
Extracted from CategoryTheory/Countable.lean
Genuine: 5 of 20 | Dissolved: 0 | Infrastructure: 15
-/
import Origin.Core

/-!
# Countable categories

A category is countable in this sense if it has countably many objects and countably many morphisms.

-/

universe w v u

noncomputable section

namespace CategoryTheory

-- INSTANCE (free from Core): discreteCountable

class CountableCategory (J : Type*) [Category* J] : Prop where
  countableObj : Countable J := by infer_instance
  countableHom : ∀ j j' : J, Countable (j ⟶ j') := by infer_instance

attribute [instance] CountableCategory.countableObj CountableCategory.countableHom

-- INSTANCE (free from Core): countableCategoryDiscreteOfCountable

-- INSTANCE (free from Core): {J

-- INSTANCE (free from Core): :

namespace CountableCategory

variable (α : Type u) [Category.{v} α] [CountableCategory α]

abbrev ObjAsType : Type :=
  InducedCategory α (equivShrink.{0} α).symm

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): {i

-- INSTANCE (free from Core): :

noncomputable def objAsTypeEquiv : ObjAsType α ≌ α :=
  (inducedFunctor (equivShrink.{0} α).symm).asEquivalence

def HomAsType := ShrinkHoms (ObjAsType α)

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): {i

-- INSTANCE (free from Core): :

noncomputable def homAsTypeEquiv : HomAsType α ≌ α :=
  (ShrinkHoms.equivalence _).symm.trans (objAsTypeEquiv _)

end CountableCategory

-- INSTANCE (free from Core): (α

open Opposite

-- INSTANCE (free from Core): countableCategoryOpposite

attribute [local instance] uliftCategory in

-- INSTANCE (free from Core): countableCategoryUlift

end CategoryTheory
