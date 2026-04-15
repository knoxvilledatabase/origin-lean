/-
Extracted from CategoryTheory/FinCategory/Basic.lean
Genuine: 1 of 8 | Dissolved: 0 | Infrastructure: 7
-/
import Origin.Core

/-!
# Finite categories

A category is finite in this sense if it has finitely many objects, and finitely many morphisms.

## Implementation
Prior to https://github.com/leanprover-community/mathlib4/pull/14046, `FinCategory` required a `DecidableEq` instance on the object and morphism types.
This does not seem to have had any practical payoff (i.e. making some definition constructive)
so we have removed these requirements to avoid
having to supply instances or delay with non-defeq conflicts between instances.
-/

universe w v u

noncomputable section

namespace CategoryTheory

-- INSTANCE (free from Core): discreteFintype

-- INSTANCE (free from Core): {α

-- INSTANCE (free from Core): discreteHomFintype

class FinCategory (J : Type v) [SmallCategory J] where
  fintypeObj : Fintype J := by infer_instance
  fintypeHom : ∀ j j' : J, Fintype (j ⟶ j') := by infer_instance

attribute [instance_reducible, instance] FinCategory.fintypeObj FinCategory.fintypeHom

-- INSTANCE (free from Core): finCategoryDiscreteOfFintype

-- INSTANCE (free from Core): {J

open Opposite

-- INSTANCE (free from Core): finCategoryOpposite

attribute [local instance] uliftCategory in

-- INSTANCE (free from Core): finCategoryUlift

end CategoryTheory
