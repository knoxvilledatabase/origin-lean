/-
Extracted from CategoryTheory/ChosenFiniteProducts/Cat.lean
Genuine: 4 | Conflates: 0 | Dissolved: 0 | Infrastructure: 16
-/
import Origin.Core
import Mathlib.CategoryTheory.ChosenFiniteProducts

noncomputable section

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

end CategoryTheory.Monoidal
