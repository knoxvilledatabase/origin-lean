/-
Extracted from CategoryTheory/ConcreteCategory/ReflectsIso.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
A `forget₂ C D` forgetful functor between concrete categories `C` and `D`
whose forgetful functors both reflect isomorphisms, itself reflects isomorphisms.
-/

universe u

namespace CategoryTheory

-- INSTANCE (free from Core): :

variable (C : Type (u + 1)) [Category* C]
    {FC : outParam <| C → C → Type u} {CC : outParam <| C → Type u}
    [outParam <| ∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{u} C FC]

variable (D : Type (u + 1)) [Category* D]
    {FD : outParam <| D → D → Type u} {CD : outParam <| D → Type u}
    [outParam <| ∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory.{u} D FD]

theorem reflectsIsomorphisms_forget₂ [HasForget₂ C D] [(forget C).ReflectsIsomorphisms] :
    (forget₂ C D).ReflectsIsomorphisms :=
  { reflects := fun X Y f {i} => by
      haveI i' : IsIso ((forget D).map ((forget₂ C D).map f)) := Functor.map_isIso (forget D) _
      haveI : IsIso ((forget C).map f) := by
        rwa [← @HasForget₂.forget_comp C _ _ _ _ _ D _ _ _ _ _]
      apply isIso_of_reflects_iso f (forget C) }

end CategoryTheory
