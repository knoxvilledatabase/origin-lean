/-
Extracted from Topology/Category/FinTopCat.lean
Genuine: 2 of 13 | Dissolved: 0 | Infrastructure: 11
-/
import Origin.Core
import Mathlib.CategoryTheory.FintypeCat
import Mathlib.Topology.Category.TopCat.Basic

/-!
# Category of finite topological spaces

Definition of the category of finite topological spaces with the canonical
forgetful functors.

-/

universe u

open CategoryTheory

structure FinTopCat where
  /-- carrier of a finite topological space. -/
  toTop : TopCat.{u}
  [fintype : Fintype toTop]

namespace FinTopCat

instance : Inhabited FinTopCat :=
  ⟨{ toTop := { α := PEmpty } }⟩

instance : CoeSort FinTopCat (Type u) :=
  ⟨fun X => X.toTop⟩

attribute [instance] fintype

instance : Category FinTopCat :=
  InducedCategory.category toTop

instance : ConcreteCategory FinTopCat :=
  InducedCategory.concreteCategory _

instance (X : FinTopCat) : TopologicalSpace ((forget FinTopCat).obj X) :=
  inferInstanceAs <| TopologicalSpace X

instance (X : FinTopCat) : Fintype ((forget FinTopCat).obj X) :=
  X.fintype

def of (X : Type u) [Fintype X] [TopologicalSpace X] : FinTopCat where
  toTop := TopCat.of X
  fintype := ‹_›

@[simp]
theorem coe_of (X : Type u) [Fintype X] [TopologicalSpace X] :
    (of X : Type u) = X :=
  rfl

instance : HasForget₂ FinTopCat FintypeCat :=
  HasForget₂.mk' (fun X ↦ FintypeCat.of X) (fun _ ↦ rfl) (fun f ↦ f.toFun) HEq.rfl

instance (X : FinTopCat) : TopologicalSpace ((forget₂ FinTopCat FintypeCat).obj X) :=
  inferInstanceAs <| TopologicalSpace X

instance : HasForget₂ FinTopCat TopCat :=
  InducedCategory.hasForget₂ _

instance (X : FinTopCat) : Fintype ((forget₂ FinTopCat TopCat).obj X) :=
  X.fintype

end FinTopCat
