/-
Extracted from Condensed/Light/Basic.lean
Genuine: 4 of 7 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Topology.Category.LightProfinite.EffectiveEpi

/-!

# Light condensed objects

This file defines the category of light condensed objects in a category `C`, following the work
of Clausen-Scholze (see https://www.youtube.com/playlist?list=PLx5f8IelFRgGmu6gmL-Kf_Rl_6Mm7juZO).

-/

universe u v w

open CategoryTheory Limits

def LightCondensed (C : Type w) [Category.{v} C] :=
  Sheaf (coherentTopology LightProfinite.{u}) C

instance {C : Type w} [Category.{v} C] : Category (LightCondensed.{u} C) :=
  show Category (Sheaf _ _) from inferInstance

abbrev LightCondSet := LightCondensed.{u} (Type u)

namespace LightCondensed

variable {C : Type w} [Category.{v} C]

@[simp]
lemma id_val (X : LightCondensed.{u} C) : (𝟙 X : X ⟶ X).val = 𝟙 _ := rfl

@[simp]
lemma comp_val {X Y Z : LightCondensed.{u} C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).val = f.val ≫ g.val :=
  rfl

@[ext]
lemma hom_ext {X Y : LightCondensed.{u} C} (f g : X ⟶ Y) (h : ∀ S, f.val.app S = g.val.app S) :
    f = g := by
  apply Sheaf.hom_ext
  ext
  exact h _

end LightCondensed

namespace LightCondSet

@[simp]
lemma hom_naturality_apply {X Y : LightCondSet.{u}} (f : X ⟶ Y) {S T : LightProfiniteᵒᵖ}
    (g : S ⟶ T) (x : X.val.obj S) : f.val.app T (X.val.map g x) = Y.val.map g (f.val.app S x) :=
  NatTrans.naturality_apply f.val g x

end LightCondSet
