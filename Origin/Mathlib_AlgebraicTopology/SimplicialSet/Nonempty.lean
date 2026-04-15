/-
Extracted from AlgebraicTopology/SimplicialSet/Nonempty.lean
Genuine: 4 of 9 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-!
# Nonempty simplicial sets

-/

universe u

open Simplicial CategoryTheory Limits

namespace SSet

variable (X : SSet.{u})

protected abbrev Nonempty : Prop := _root_.Nonempty (X _⦋0⦌)

-- INSTANCE (free from Core): (n

-- INSTANCE (free from Core): [X.Nonempty]

-- INSTANCE (free from Core): [X.Nonempty]

-- INSTANCE (free from Core): (T

-- INSTANCE (free from Core): (n

variable {X} in

lemma nonempty_of_hom {Y : SSet.{u}} (f : Y ⟶ X) [Y.Nonempty] : X.Nonempty :=
  ⟨f.app _ (Classical.arbitrary _)⟩

lemma notNonempty_iff_hasDimensionLT_zero :
    ¬ X.Nonempty ↔ X.HasDimensionLT 0 := by
  simp only [not_nonempty_iff]
  refine ⟨fun _ ↦ ⟨fun n hn ↦ ?_⟩, fun _ ↦ ⟨fun x ↦ ?_⟩⟩
  · have := Function.isEmpty (X.map (⦋0⦌.const ⦋n⦌ 0).op)
    subsingleton
  · exact (lt_self_iff_false _).1 (X.dim_lt_of_nonDegenerate ⟨x, by simp⟩ 0)

variable {X} in

def isInitialOfNotNonempty (hX : ¬ X.Nonempty) : IsInitial X := by
  simp only [not_nonempty_iff] at hX
  have (n : SimplexCategoryᵒᵖ) : IsEmpty (X.obj n) :=
    Function.isEmpty (X.map (⦋0⦌.const n.unop 0).op)
  exact IsInitial.ofUniqueHom (fun _ ↦
    { app _ := TypeCat.ofHom fun x ↦ isEmptyElim x
      naturality _ _ _  := by ext x; exact isEmptyElim x })
    (fun _ _ ↦ by ext _ x; exact isEmptyElim x)

end SSet
