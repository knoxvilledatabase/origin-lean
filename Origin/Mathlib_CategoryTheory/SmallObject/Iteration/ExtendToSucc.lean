/-
Extracted from CategoryTheory/SmallObject/Iteration/ExtendToSucc.lean
Genuine: 8 of 8 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Extension of a functor from `Set.Iic j` to `Set.Iic (Order.succ j)`

Given a linearly ordered type `J` with `SuccOrder J`, `j : J` that is not maximal,
we define the extension of a functor `F : Set.Iic j ⥤ C` as a
functor `Set.Iic (Order.succ j) ⥤ C` when an object `X : C` and a morphism
`τ : F.obj ⟨j, _⟩ ⟶ X` is given.

-/

universe u

namespace CategoryTheory

open Category

namespace SmallObject

variable {C : Type*} [Category* C]
  {J : Type u} [LinearOrder J] [SuccOrder J] {j : J} (hj : ¬IsMax j)
  (F : Set.Iic j ⥤ C) {X : C} (τ : F.obj ⟨j, by simp⟩ ⟶ X)

namespace SuccStruct

namespace extendToSucc

variable (X)

set_option backward.privateInPublic true in

def obj (i : Set.Iic (Order.succ j)) : C :=
  if hij : i.1 ≤ j then F.obj ⟨i.1, hij⟩ else X

lemma obj_eq (i : Set.Iic j) :
    obj F X ⟨i, i.2.trans (Order.le_succ j)⟩ = F.obj i := dif_pos i.2

def objIso (i : Set.Iic j) :
    obj F X ⟨i, i.2.trans (Order.le_succ j)⟩ ≅ F.obj i :=
  eqToIso (obj_eq _ _ _)

include hj in

lemma obj_succ_eq : obj F X ⟨Order.succ j, by simp⟩ = X :=
  dif_neg (by simpa only [Order.succ_le_iff_isMax] using hj)

def objSuccIso :
    obj F X ⟨Order.succ j, by simp⟩ ≅ X :=
  eqToIso (obj_succ_eq hj _ _)

variable {X}

def map (i₁ i₂ : J) (hi : i₁ ≤ i₂) (hi₂ : i₂ ≤ Order.succ j) :
    obj F X ⟨i₁, hi.trans hi₂⟩ ⟶ obj F X ⟨i₂, hi₂⟩ :=
  if h₁ : i₂ ≤ j then
    (objIso F X ⟨i₁, hi.trans h₁⟩).hom ≫ F.map (homOfLE hi) ≫ (objIso F X ⟨i₂, h₁⟩).inv
  else
    if h₂ : i₁ ≤ j then
      (objIso F X ⟨i₁, h₂⟩).hom ≫ F.map (homOfLE h₂) ≫ τ ≫
        (objSuccIso hj F X).inv ≫ eqToHom (by
          congr
          exact le_antisymm (Order.succ_le_of_lt (not_le.1 h₁)) hi₂)
    else
      eqToHom (by
        congr
        rw [le_antisymm hi₂ (Order.succ_le_of_lt (not_le.1 h₁)),
          le_antisymm (hi.trans hi₂) (Order.succ_le_of_lt (not_le.1 h₂))])

lemma map_eq (i₁ i₂ : J) (hi : i₁ ≤ i₂) (hi₂ : i₂ ≤ j) :
    map hj F τ i₁ i₂ hi (hi₂.trans (Order.le_succ j)) =
      (objIso F X ⟨i₁, hi.trans hi₂⟩).hom ≫ F.map (homOfLE hi) ≫
        (objIso F X ⟨i₂, hi₂⟩).inv :=
  dif_pos hi₂

lemma map_self_succ :
    map hj F τ j (Order.succ j) (Order.le_succ j) (by rfl) =
      (objIso F X ⟨j, by simp⟩).hom ≫ τ ≫ (objSuccIso hj F X).inv := by
  dsimp [map]
  rw [dif_neg (by simpa only [Order.succ_le_iff_isMax] using hj),
    dif_pos (by rfl), Functor.map_id, comp_id, id_comp]
