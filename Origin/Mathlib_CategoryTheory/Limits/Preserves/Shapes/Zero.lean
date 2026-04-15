/-
Extracted from CategoryTheory/Limits/Preserves/Shapes/Zero.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Preservation of zero objects and zero morphisms

We define the class `PreservesZeroMorphisms` and show basic properties.

## Main results

We provide the following results:
* Left adjoints and right adjoints preserve zero morphisms;
* full functors preserve zero morphisms;
* if both categories involved have a zero object, then a functor preserves zero morphisms if and
  only if it preserves the zero object;
* functors which preserve initial or terminal objects preserve zero morphisms.

-/

universe v u v₁ v₂ v₃ u₁ u₂ u₃

noncomputable section

open CategoryTheory

open CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {E : Type u₃} [Category.{v₃} E]

section ZeroMorphisms

variable [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroMorphisms E]

class PreservesZeroMorphisms (F : C ⥤ D) : Prop where
  /-- For any pair objects `F (0: X ⟶ Y) = (0 : F X ⟶ F Y)` -/
  map_zero : ∀ X Y : C, F.map (0 : X ⟶ Y) = 0 := by aesop
