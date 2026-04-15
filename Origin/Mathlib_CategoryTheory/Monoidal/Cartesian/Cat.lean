/-
Extracted from CategoryTheory/Monoidal/Cartesian/Cat.lean
Genuine: 5 of 22 | Dissolved: 0 | Infrastructure: 17
-/
import Origin.Core

/-!
# Chosen finite products in `Cat`

This file proves that the Cartesian product of a pair of categories agrees with the
product in `Cat`, and provides the associated `CartesianMonoidalCategory` instance.
-/

universe v u

namespace CategoryTheory

namespace Cat

open Limits

attribute [local instance] uliftCategory in

abbrev chosenTerminal : Cat.{v, u} := Cat.of (ULift (ULiftHom (Discrete Unit)))

attribute [local instance] uliftCategory in

def chosenTerminalIsTerminal : IsTerminal chosenTerminal.{v, u} :=
  IsTerminal.ofUniqueHom (fun C ↦ ((Functor.const C).obj ⟨⟨⟨⟩⟩⟩).toCatHom) fun _ _ ↦ rfl

set_option backward.isDefEq.respectTransparency false in

def fromChosenTerminalEquiv {C : Type u} [Category.{v} C] : Cat.chosenTerminal ⥤ C ≃ C where
  toFun F := F.obj ⟨⟨()⟩⟩
  invFun := (Functor.const _).obj
  left_inv _ := by
    apply Functor.ext
    · rintro ⟨⟨⟨⟩⟩⟩ ⟨⟨⟨⟩⟩⟩ ⟨⟨⟨⟨⟩⟩⟩⟩
      simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
      exact (Functor.map_id _ _).symm
    · intro; rfl
  right_inv _ := rfl

def prodCone (C D : Cat.{v, u}) : BinaryFan C D :=
  .mk (P := .of (C × D)) (Prod.fst _ _).toCatHom (Prod.snd _ _).toCatHom

def isLimitProdCone (X Y : Cat) : IsLimit (prodCone X Y) := BinaryFan.isLimitMk
  (fun S => (S.fst.toFunctor.prod' S.snd.toFunctor).toCatHom) (fun _ => rfl)
    (fun _ => rfl) (fun _ _ h1 h2 => Cat.Hom.ext <| Functor.hext
      (fun _ ↦ Prod.ext (by simp [← h1]) (by simp [← h2]))
      (fun _ _ _ ↦ by dsimp; rw [← h1, ← h2]; rfl))

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

example : MonoidalCategory Cat := by infer_instance

example : SymmetricCategory Cat := by infer_instance

end Cat

namespace Monoidal

open MonoidalCategory

end CategoryTheory.Monoidal
