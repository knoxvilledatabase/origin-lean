/-
Extracted from CategoryTheory/ChosenFiniteProducts/Cat.lean
Genuine: 4 | Conflates: 0 | Dissolved: 0 | Infrastructure: 16
-/
import Origin.Core
import Mathlib.CategoryTheory.ChosenFiniteProducts

/-!
# Chosen finite products in `Cat`

This file proves that the cartesian product of a pair of categories agrees with the
product in `Cat`, and provides the associated `ChosenFiniteProducts` instance.
-/

universe v u

namespace CategoryTheory

namespace Cat

open Limits

abbrev chosenTerminal : Cat := Cat.of (ULift (ULiftHom (Discrete Unit)))

def chosenTerminalIsTerminal : IsTerminal chosenTerminal :=
  IsTerminal.ofUniqueHom (fun _ ↦ (Functor.const _).obj ⟨⟨⟨⟩⟩⟩) fun _ _ ↦ rfl

def prodCone (C D : Cat.{v,u}) : BinaryFan C D :=
  .mk (P := .of (C × D)) (Prod.fst _ _) (Prod.snd _ _)

def isLimitProdCone (X Y : Cat) : IsLimit (prodCone X Y) := BinaryFan.isLimitMk
  (fun S => S.fst.prod' S.snd) (fun _ => rfl) (fun _ => rfl) (fun _ _ h1 h2 =>
    Functor.hext
      (fun _ ↦ Prod.ext (by simp [← h1]) (by simp [← h2]))
      (fun _ _ _ ↦ by dsimp; rw [← h1, ← h2]; rfl))

instance : ChosenFiniteProducts Cat where
  product (X Y : Cat) := { isLimit := isLimitProdCone X Y }
  terminal  := { isLimit := chosenTerminalIsTerminal }

example : MonoidalCategory Cat := by infer_instance

example : SymmetricCategory Cat := by infer_instance

end Cat

namespace Monoidal

open MonoidalCategory

lemma tensorObj (C : Cat) (D : Cat) : C ⊗ D = Cat.of (C × D) := rfl

lemma whiskerLeft (X : Cat) {A : Cat} {B : Cat} (f : A ⟶ B) :
    X ◁ f = (𝟭 X).prod f := rfl

lemma whiskerLeft_fst (X : Cat) {A : Cat} {B : Cat} (f : A ⟶ B) :
    (X ◁ f) ⋙ Prod.fst _ _ = Prod.fst _ _ := rfl

lemma whiskerLeft_snd (X : Cat) {A : Cat} {B : Cat} (f : A ⟶ B) :
    (X ◁ f) ⋙ Prod.snd _ _ = Prod.snd _ _ ⋙ f := rfl

lemma whiskerRight {A : Cat} {B : Cat} (f : A ⟶ B) (X : Cat) :
    f ▷  X  = f.prod (𝟭 X) := rfl

lemma whiskerRight_fst {A : Cat} {B : Cat} (f : A ⟶ B) (X : Cat) :
    (f ▷ X) ⋙ Prod.fst _ _  = Prod.fst _ _ ⋙ f := rfl

lemma whiskerRight_snd {A : Cat} {B : Cat} (f : A ⟶ B) (X : Cat) :
    (f ▷ X) ⋙ Prod.snd _ _  = Prod.snd _ _ := rfl

lemma tensorHom {A : Cat} {B : Cat} (f : A ⟶ B) {X : Cat} {Y : Cat} (g : X ⟶ Y) :
    f ⊗ g = f.prod g := rfl

lemma tensorUnit : 𝟙_ Cat = Cat.chosenTerminal := rfl

lemma associator_hom (X : Cat) (Y : Cat) (Z : Cat) :
    (associator X Y Z).hom = Functor.prod' (Prod.fst (X × Y) Z ⋙ Prod.fst X Y)
      ((Functor.prod' ((Prod.fst (X × Y) Z ⋙ Prod.snd X Y))
      (Prod.snd (X × Y) Z : (X × Y) × Z ⥤ Z))) := rfl

lemma associator_inv (X : Cat) (Y : Cat) (Z : Cat) :
    (associator X Y Z).inv = Functor.prod' (Functor.prod' (Prod.fst X (Y × Z) : X × (Y × Z) ⥤ X)
      (Prod.snd X (Y × Z) ⋙ Prod.fst Y Z)) (Prod.snd X (Y × Z) ⋙ Prod.snd Y Z) := rfl

lemma leftUnitor_hom (C : Cat) : (λ_ C).hom = Prod.snd _ _ := rfl

lemma leftUnitor_inv (C : Cat) : (λ_ C).inv = Prod.sectR ⟨⟨⟨⟩⟩⟩ _ := rfl

lemma rightUnitor_hom (C : Cat) : (ρ_ C).hom = Prod.fst _ _ := rfl

lemma rightUnitor_inv (C : Cat) : (ρ_ C).inv = Prod.sectL _ ⟨⟨⟨⟩⟩⟩ := rfl

end CategoryTheory.Monoidal
