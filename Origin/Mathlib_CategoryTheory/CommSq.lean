/-
Extracted from CategoryTheory/CommSq.lean
Genuine: 12 of 12 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Commutative squares

This file provides an API for commutative squares in categories.
If `top`, `left`, `right` and `bottom` are four morphisms which are the edges
of a square, `CommSq top left right bottom` is the predicate that this
square is commutative.

The structure `CommSq` is extended in
`Mathlib/CategoryTheory/Limits/Shapes/Pullback/IsPullback/Defs.lean`
as `IsPullback` and `IsPushout` in order to define pullback and pushout squares.

## Future work

Refactor `LiftStruct` from `Arrow.lean` and lifting properties using `CommSq.lean`.

-/

namespace CategoryTheory

variable {C : Type*} [Category* C]

structure CommSq {W X Y Z : C} (f : W ⟶ X) (g : W ⟶ Y) (h : X ⟶ Z) (i : Y ⟶ Z) : Prop where
  /-- The square commutes. -/
  w : f ≫ h = g ≫ i := by cat_disch

attribute [reassoc] CommSq.w

attribute [simp] CommSq.mk

namespace CommSq

variable {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}

theorem flip (p : CommSq f g h i) : CommSq g f i h :=
  ⟨p.w.symm⟩

theorem of_arrow {f g : Arrow C} (h : f ⟶ g) : CommSq f.hom h.left h.right g.hom :=
  ⟨h.w.symm⟩

theorem op (p : CommSq f g h i) : CommSq i.op h.op g.op f.op :=
  ⟨by simp only [← op_comp, p.w]⟩

theorem unop {W X Y Z : Cᵒᵖ} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z} (p : CommSq f g h i) :
    CommSq i.unop h.unop g.unop f.unop :=
  ⟨by simp only [← unop_comp, p.w]⟩

theorem vert_inv {g : W ≅ Y} {h : X ≅ Z} (p : CommSq f g.hom h.hom i) :
    CommSq i g.inv h.inv f :=
  ⟨by rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, p.w]⟩

theorem horiz_inv {f : W ≅ X} {i : Y ≅ Z} (p : CommSq f.hom g h i.hom) :
    CommSq f.inv h g i.inv :=
  flip (vert_inv (flip p))

lemma horiz_comp {W X X' Y Z Z' : C} {f : W ⟶ X} {f' : X ⟶ X'} {g : W ⟶ Y} {h : X ⟶ Z}
    {h' : X' ⟶ Z'} {i : Y ⟶ Z} {i' : Z ⟶ Z'} (hsq₁ : CommSq f g h i) (hsq₂ : CommSq f' h h' i') :
    CommSq (f ≫ f') g h' (i ≫ i') :=
  ⟨by rw [← Category.assoc, Category.assoc, ← hsq₁.w, hsq₂.w, Category.assoc]⟩

lemma vert_comp {W X Y Y' Z Z' : C} {f : W ⟶ X} {g : W ⟶ Y} {g' : Y ⟶ Y'} {h : X ⟶ Z}
    {h' : Z ⟶ Z'} {i : Y ⟶ Z} {i' : Y' ⟶ Z'} (hsq₁ : CommSq f g h i) (hsq₂ : CommSq i g' h' i') :
    CommSq f (g ≫ g') (h ≫ h') i' :=
  flip (horiz_comp (flip hsq₁) (flip hsq₂))

variable {W X Y : C}

theorem eq_of_mono {f : W ⟶ X} {g : W ⟶ X} {i : X ⟶ Y} [Mono i] (sq : CommSq f g i i) : f = g :=
  (cancel_mono i).1 sq.w

theorem eq_of_epi {f : W ⟶ X} {h : X ⟶ Y} {i : X ⟶ Y} [Epi f] (sq : CommSq f f h i) : h = i :=
  (cancel_epi f).1 sq.w

end

end CommSq

namespace Functor

variable {D : Type*} [Category* D]

variable (F : C ⥤ D) {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}

theorem map_commSq (s : CommSq f g h i) : CommSq (F.map f) (F.map g) (F.map h) (F.map i) :=
  ⟨by simpa using congr_arg (fun k : W ⟶ Z => F.map k) s.w⟩

end Functor

alias CommSq.map := Functor.map_commSq

namespace CommSq

variable {A B X Y : C} {f : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y}
