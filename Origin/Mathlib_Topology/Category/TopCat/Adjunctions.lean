/-
Extracted from Topology/Category/TopCat/Adjunctions.lean
Genuine: 2 | Conflates: 0 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.CategoryTheory.Adjunction.Basic

noncomputable section

/-!
# Adjunctions regarding the category of topological spaces

This file shows that the forgetful functor from topological spaces to types has a left and right
adjoint, given by `TopCat.discrete`, resp. `TopCat.trivial`, the functors which equip a type with
the discrete, resp. trivial, topology.
-/

universe u

open CategoryTheory

open TopCat

namespace TopCat

@[simps! unit counit]
def adj₁ : discrete ⊣ forget TopCat.{u} where
  unit := { app := fun _ => id }
  counit := { app := fun _ => ⟨id, continuous_bot⟩ }

@[simps! unit counit]
def adj₂ : forget TopCat.{u} ⊣ trivial where
  unit := { app := fun _ => ⟨id, continuous_top⟩ }
  counit := { app := fun _ => id }

instance : (forget TopCat.{u}).IsRightAdjoint :=
  ⟨_, ⟨adj₁⟩⟩

instance : (forget TopCat.{u}).IsLeftAdjoint :=
  ⟨_, ⟨adj₂⟩⟩

end TopCat
