/-
Extracted from Combinatorics/Quiver/Basic.lean
Genuine: 6 | Conflates: 0 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core
import Mathlib.Data.Opposite

noncomputable section

/-!
# Quivers

This module defines quivers. A quiver on a type `V` of vertices assigns to every
pair `a b : V` of vertices a type `a ⟶ b` of arrows from `a` to `b`. This
is a very permissive notion of directed graph.

## Implementation notes

Currently `Quiver` is defined with `Hom : V → V → Sort v`.
This is different from the category theory setup,
where we insist that morphisms live in some `Type`.
There's some balance here: it's nice to allow `Prop` to ensure there are no multiple arrows,
but it is also results in error-prone universe signatures when constraints require a `Type`.
-/

open Opposite

universe v v₁ v₂ u u₁ u₂

class Quiver (V : Type u) where
  /-- The type of edges/arrows/morphisms between a given source and target. -/
  Hom : V → V → Sort v

infixr:10 " ⟶ " => Quiver.Hom

namespace Quiver

instance opposite {V} [Quiver V] : Quiver Vᵒᵖ :=
  ⟨fun a b => (unop b ⟶ unop a)ᵒᵖ⟩

def Hom.op {V} [Quiver V] {X Y : V} (f : X ⟶ Y) : op Y ⟶ op X := ⟨f⟩

def Hom.unop {V} [Quiver V] {X Y : Vᵒᵖ} (f : X ⟶ Y) : unop Y ⟶ unop X := Opposite.unop f

@[simps]
def Hom.opEquiv {V} [Quiver V] {X Y : V} :
    (X ⟶ Y) ≃ (Opposite.op Y ⟶ Opposite.op X) where
  toFun := Opposite.op
  invFun := Opposite.unop
  left_inv _ := rfl
  right_inv _ := rfl

def Empty (V : Type u) : Type u := V

instance emptyQuiver (V : Type u) : Quiver.{u} (Empty V) := ⟨fun _ _ => PEmpty⟩

@[simp]
theorem empty_arrow {V : Type u} (a b : Empty V) : (a ⟶ b) = PEmpty := rfl

abbrev IsThin (V : Type u) [Quiver V] : Prop := ∀ a b : V, Subsingleton (a ⟶ b)

end Quiver
