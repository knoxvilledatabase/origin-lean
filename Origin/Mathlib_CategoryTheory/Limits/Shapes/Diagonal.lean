/-
Extracted from CategoryTheory/Limits/Shapes/Diagonal.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The diagonal object of a morphism.

We provide various API and isomorphisms considering the diagonal object `Δ_{Y/X} := pullback f f`
of a morphism `f : X ⟶ Y`.

-/

open CategoryTheory

noncomputable section

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C] {X Y Z : C}

namespace pullback

section Diagonal

variable (f : X ⟶ Y) [HasPullback f f]

abbrev diagonalObj : C :=
  pullback f f

def diagonal : X ⟶ diagonalObj f :=
  pullback.lift (𝟙 _) (𝟙 _) rfl
