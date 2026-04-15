/-
Extracted from CategoryTheory/Dialectica/Monoidal.lean
Genuine: 19 of 22 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Dialectica.Basic

/-!
# The Dialectica category is symmetric monoidal

We show that the category `Dial` has a symmetric monoidal category structure.
-/

noncomputable section

namespace CategoryTheory

open MonoidalCategory Limits

universe v u

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] [HasPullbacks C]

namespace Dial

local notation "π₁" => prod.fst

local notation "π₂" => prod.snd

local notation "π(" a ", " b ")" => prod.lift a b

@[simps] def tensorObj (X Y : Dial C) : Dial C where
  src := X.src ⨯ Y.src
  tgt := X.tgt ⨯ Y.tgt
  rel :=
    (Subobject.pullback (prod.map π₁ π₁)).obj X.rel ⊓
    (Subobject.pullback (prod.map π₂ π₂)).obj Y.rel

@[simps] def tensorHom {X₁ X₂ Y₁ Y₂ : Dial C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) :
    tensorObj X₁ Y₁ ⟶ tensorObj X₂ Y₂ where
  f := prod.map f.f g.f
  F := π(prod.map π₁ π₁ ≫ f.F, prod.map π₂ π₂ ≫ g.F)
  le := by
    simp only [tensorObj, Subobject.inf_pullback]
    apply inf_le_inf <;> rw [← Subobject.pullback_comp, ← Subobject.pullback_comp]
    · have := (Subobject.pullback (prod.map π₁ π₁ :
        (X₁.src ⨯ Y₁.src) ⨯ X₂.tgt ⨯ Y₂.tgt ⟶ _)).monotone (Hom.le f)
      rw [← Subobject.pullback_comp, ← Subobject.pullback_comp] at this
      convert this using 3 <;> simp
    · have := (Subobject.pullback (prod.map π₂ π₂ :
        (X₁.src ⨯ Y₁.src) ⨯ X₂.tgt ⨯ Y₂.tgt ⟶ _)).monotone (Hom.le g)
      rw [← Subobject.pullback_comp, ← Subobject.pullback_comp] at this
      convert this using 3 <;> simp

@[simps] def tensorUnit : Dial C := { src := ⊤_ _, tgt := ⊤_ _, rel := ⊤ }

@[simps!] def leftUnitor (X : Dial C) : tensorObj tensorUnit X ≅ X :=
  isoMk (Limits.prod.leftUnitor _) (Limits.prod.leftUnitor _) <| by simp [Subobject.pullback_top]

@[simps!] def rightUnitor (X : Dial C) : tensorObj X tensorUnit ≅ X :=
  isoMk (Limits.prod.rightUnitor _) (Limits.prod.rightUnitor _) <| by simp [Subobject.pullback_top]

@[simps!]
def associator (X Y Z : Dial C) : tensorObj (tensorObj X Y) Z ≅ tensorObj X (tensorObj Y Z) :=
  isoMk (prod.associator ..) (prod.associator ..) <| by
    simp [Subobject.inf_pullback, ← Subobject.pullback_comp, inf_assoc]

@[simps!]
instance : MonoidalCategoryStruct (Dial C) where
  tensorUnit := tensorUnit
  tensorObj := tensorObj
  whiskerLeft X _ _ f := tensorHom (𝟙 X) f
  whiskerRight f Y := tensorHom f (𝟙 Y)
  tensorHom := tensorHom
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor
  associator := associator

theorem tensor_id (X₁ X₂ : Dial C) : (𝟙 X₁ ⊗ 𝟙 X₂ : _ ⟶ _) = 𝟙 (X₁ ⊗ X₂ : Dial C) := by aesop_cat

theorem tensor_comp {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : Dial C}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
    tensorHom (f₁ ≫ g₁) (f₂ ≫ g₂) = tensorHom f₁ f₂ ≫ tensorHom g₁ g₂ := by
  ext <;> simp; ext <;> simp <;> (rw [← Category.assoc]; congr 1; simp)

theorem associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Dial C}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
    tensorHom (tensorHom f₁ f₂) f₃ ≫ (associator Y₁ Y₂ Y₃).hom =
    (associator X₁ X₂ X₃).hom ≫ tensorHom f₁ (tensorHom f₂ f₃) := by aesop_cat

theorem leftUnitor_naturality {X Y : Dial C} (f : X ⟶ Y) :
    (𝟙 (𝟙_ (Dial C)) ⊗ f) ≫ (λ_ Y).hom = (λ_ X).hom ≫ f := by
  ext <;> simp; ext; simp; congr 1; ext <;> simp

theorem rightUnitor_naturality {X Y : Dial C} (f : X ⟶ Y) :
    (f ⊗ 𝟙 (𝟙_ (Dial C))) ≫ (ρ_ Y).hom = (ρ_ X).hom ≫ f := by
  ext <;> simp; ext; simp; congr 1; ext <;> simp

theorem pentagon (W X Y Z : Dial C) :
    (tensorHom (associator W X Y).hom (𝟙 Z)) ≫ (associator W (tensorObj X Y) Z).hom ≫
      (tensorHom (𝟙 W) (associator X Y Z).hom) =
    (associator (tensorObj W X) Y Z).hom ≫ (associator W X (tensorObj Y Z)).hom := by
  ext <;> simp

theorem triangle (X Y : Dial C) :
    (associator X (𝟙_ (Dial C)) Y).hom ≫ tensorHom (𝟙 X) (leftUnitor Y).hom =
    tensorHom (rightUnitor X).hom (𝟙 Y) := by aesop_cat

instance : MonoidalCategory (Dial C) :=
  .ofTensorHom
    (tensor_id := tensor_id)
    (tensor_comp := tensor_comp)
    (associator_naturality := associator_naturality)
    (leftUnitor_naturality := leftUnitor_naturality)
    (rightUnitor_naturality := rightUnitor_naturality)
    (pentagon := pentagon)
    (triangle := triangle)

@[simps!] def braiding (X Y : Dial C) : tensorObj X Y ≅ tensorObj Y X :=
  isoMk (prod.braiding ..) (prod.braiding ..) <| by
    simp [Subobject.inf_pullback, ← Subobject.pullback_comp, inf_comm]

theorem symmetry (X Y : Dial C) :
    (braiding X Y).hom ≫ (braiding Y X).hom = 𝟙 (tensorObj X Y) := by aesop_cat

theorem braiding_naturality_right (X : Dial C) {Y Z : Dial C} (f : Y ⟶ Z) :
    tensorHom (𝟙 X) f ≫ (braiding X Z).hom = (braiding X Y).hom ≫ tensorHom f (𝟙 X) := by aesop_cat

theorem braiding_naturality_left {X Y : Dial C} (f : X ⟶ Y) (Z : Dial C) :
    tensorHom f (𝟙 Z) ≫ (braiding Y Z).hom = (braiding X Z).hom ≫ tensorHom (𝟙 Z) f := by aesop_cat

theorem hexagon_forward (X Y Z : Dial C) :
    (associator X Y Z).hom ≫ (braiding X (Y ⊗ Z)).hom ≫ (associator Y Z X).hom =
      tensorHom (braiding X Y).hom (𝟙 Z) ≫ (associator Y X Z).hom ≫
      tensorHom (𝟙 Y) (braiding X Z).hom := by aesop_cat

theorem hexagon_reverse (X Y Z : Dial C) :
    (associator X Y Z).inv ≫ (braiding (X ⊗ Y) Z).hom ≫ (associator Z X Y).inv =
      tensorHom (𝟙 X) (braiding Y Z).hom ≫ (associator X Z Y).inv ≫
      tensorHom (braiding X Z).hom (𝟙 Y) := by aesop_cat

instance : SymmetricCategory (Dial C) where
  braiding := braiding
  braiding_naturality_right := braiding_naturality_right
  braiding_naturality_left := braiding_naturality_left
  hexagon_forward := hexagon_forward
  hexagon_reverse := hexagon_reverse
  symmetry := symmetry

end Dial

end CategoryTheory
