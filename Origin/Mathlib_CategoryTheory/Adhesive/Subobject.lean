/-
Extracted from CategoryTheory/Adhesive/Subobject.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!

# Subobjects in adhesive categories

## Main Results
- Subobjects in adhesive categories have binary coproducts

-/

namespace CategoryTheory.Adhesive

open Limits Subobject

universe v u

variable {C : Type u} [Category.{v} C] [Adhesive C] {X : C}

set_option backward.isDefEq.respectTransparency false in

noncomputable def isColimitBinaryCofan (a b : Subobject X) :
    IsColimit (BinaryCofan.mk (P := Subobject.mk (pushout.desc a.arrow b.arrow pullback.condition))
      (le_mk_of_comm (pushout.inl _ _) (pushout.inl_desc _ _ _)).hom
      (le_mk_of_comm (pushout.inr _ _) (pushout.inr_desc _ _ _)).hom) :=
  BinaryCofan.isColimitMk (fun s ↦ (mk_le_of_comm
      (pushout.desc (underlying.map (s.ι.app ⟨WalkingPair.left⟩))
      (underlying.map (s.ι.app ⟨WalkingPair.right⟩))
      (by ext; simp [pullback.condition])) (by cat_disch)).hom)
    (by intros; rfl) (by intros; rfl) (by intros; rfl)

-- INSTANCE (free from Core): [Adhesive

end CategoryTheory.Adhesive
