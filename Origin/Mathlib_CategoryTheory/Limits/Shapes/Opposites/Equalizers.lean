/-
Extracted from CategoryTheory/Limits/Shapes/Opposites/Equalizers.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Equalizers and coequalizers in `C` and `Cᵒᵖ`

We construct equalizers and coequalizers in the opposite categories.

-/

universe v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory

open CategoryTheory.Functor

open Opposite

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C]

variable {J : Type u₂} [Category.{v₂} J]

-- INSTANCE (free from Core): hasEqualizers_opposite

-- INSTANCE (free from Core): hasCoequalizers_opposite

def parallelPairOpIso {X Y : C} (f g : X ⟶ Y) :
    parallelPair f.op g.op ≅ walkingParallelPairOpEquiv.functor ⋙ (parallelPair f g).op :=
  NatIso.ofComponents (fun
    | .zero => .refl _
    | .one => .refl _)
    (by rintro (_ | _ | _) (_ | _ | _) f <;> cases f <;> cat_disch)
