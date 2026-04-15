/-
Extracted from CategoryTheory/Comma/OverClass.lean
Genuine: 11 | Conflates: 0 | Dissolved: 0 | Infrastructure: 12
-/
import Origin.Core
import Mathlib.Tactic.CategoryTheory.Reassoc
import Mathlib.CategoryTheory.Comma.Over

/-!
# Typeclasses for `S`-objects and `S`-morphisms

**Warning**: This is not usually how typeclasses should be used.
This is only a sensible approach when the morphism is considered as a structure on `X`,
typically in algebraic geometry.

This is analogous to to how we view ringhoms as structures via the `Algebra` typeclass.

For other applications use unbundled arrows or `CategoryTheory.Over`.

## Main definition
- `CategoryTheory.OverClass`: `OverClass X S` equips `X` with a morphism into `S`.
  `X ↘ S : X ⟶ S` is the structure morphism.
- `CategoryTheory.HomIsOver`:
  `HomIsOver f S` asserts that `f` commutes with the structure morphisms.

-/

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

variable {X Y Z : C} (f : X ⟶ Y) (S S' : C)

class OverClass (X S : C) : Type v where
  ofHom ::
  /-- The structure morphism. Use `X ↘ S` instead. -/
  hom : X ⟶ S

def over (X S : C) (_ : OverClass X S := by infer_instance) : X ⟶ S := OverClass.hom

notation:90 X:90 " ↘ " S:90 => CategoryTheory.over X S inferInstance

def OverClass.Simps.over (X S : C) [OverClass X S] : X ⟶ S := X ↘ S

initialize_simps_projections OverClass (hom → over)

class CanonicallyOverClass (X : C) (S : semiOutParam C) extends OverClass X S where

def CanonicallyOverClass.Simps.over (X S : C) [CanonicallyOverClass X S] : X ⟶ S := X ↘ S

initialize_simps_projections CanonicallyOverClass (hom → over)

@[simps]
instance : OverClass X X := ⟨𝟙 _⟩

instance : IsIso (S ↘ S) := inferInstanceAs (IsIso (𝟙 S))

@[simps (config := .lemmasOnly)]
instance (priority := 900) [CanonicallyOverClass X Y] [OverClass Y S] : OverClass X S :=
  ⟨X ↘ Y ≫ Y ↘ S⟩

class HomIsOver (f : X ⟶ Y) (S : C) [OverClass X S] [OverClass Y S] : Prop where
  comp_over : f ≫ Y ↘ S = X ↘ S := by aesop

@[reassoc (attr := simp)]
lemma comp_over [OverClass X S] [OverClass Y S] [HomIsOver f S] :
    f ≫ Y ↘ S = X ↘ S :=
  HomIsOver.comp_over

instance [OverClass X S] : HomIsOver (𝟙 X) S where

instance [OverClass X S] [OverClass Y S] [OverClass Z S]
    (f : X ⟶ Y) (g : Y ⟶ Z) [HomIsOver f S] [HomIsOver g S] :
    HomIsOver (f ≫ g) S where

abbrev IsOverTower (X Y S : C) [OverClass X S] [OverClass Y S] [OverClass X Y] :=
  HomIsOver (X ↘ Y) S

instance [OverClass X S] : IsOverTower X X S where

instance [OverClass X S] : IsOverTower X S S where

instance [CanonicallyOverClass X Y] [OverClass Y S] : IsOverTower X Y S :=
  ⟨rfl⟩

lemma homIsOver_of_isOverTower [OverClass X S] [OverClass X S'] [OverClass Y S]
    [OverClass Y S'] [OverClass S S']
    [IsOverTower X S S'] [IsOverTower Y S S'] [HomIsOver f S] : HomIsOver f S' := by
  constructor
  rw [← comp_over (Y ↘ S), comp_over_assoc f, comp_over]

instance [CanonicallyOverClass X S]
    [OverClass X S'] [OverClass Y S] [OverClass Y S'] [OverClass S S']
    [IsOverTower X S S'] [IsOverTower Y S S'] [HomIsOver f S] : HomIsOver f S' :=
  homIsOver_of_isOverTower f S S'

instance [OverClass X S]
    [OverClass X S'] [CanonicallyOverClass Y S] [OverClass Y S'] [OverClass S S']
    [IsOverTower X S S'] [IsOverTower Y S S'] [HomIsOver f S] : HomIsOver f S' :=
  homIsOver_of_isOverTower f S S'

variable (X) in

@[simps! hom left]
def OverClass.asOver [OverClass X S] : Over S := Over.mk (X ↘ S)

@[simps! left]
def OverClass.asOverHom [OverClass X S] [OverClass Y S] (f : X ⟶ Y) [HomIsOver f S] :
    OverClass.asOver X S ⟶ OverClass.asOver Y S :=
  Over.homMk f (comp_over f S)

@[simps]
instance OverClass.fromOver {S : C} (X : Over S) : OverClass X.left S where
  hom := X.hom

instance {S : C} {X Y : Over S} (f : X ⟶ Y) : HomIsOver f.left S where
  comp_over := Over.w f

end CategoryTheory
