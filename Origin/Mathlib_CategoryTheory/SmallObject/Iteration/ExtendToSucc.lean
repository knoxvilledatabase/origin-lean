/-
Extracted from CategoryTheory/SmallObject/Iteration/ExtendToSucc.lean
Genuine: 15 of 15 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.CategoryTheory.SmallObject.Iteration.Basic

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

namespace Functor

variable {C : Type*} [Category C]
  {J : Type u} [LinearOrder J] [SuccOrder J] {j : J} (hj : ¬IsMax j)
  (F : Set.Iic j ⥤ C) {X : C} (τ : F.obj ⟨j, by simp⟩ ⟶ X)

namespace extendToSucc

variable (X)

def obj (i : Set.Iic (Order.succ j)) : C :=
  if hij : i.1 ≤ j then F.obj ⟨i.1, hij⟩ else X

def objIso (i : Set.Iic j) :
    obj F X ⟨i, i.2.trans (Order.le_succ j)⟩ ≅ F.obj i := eqToIso (dif_pos i.2)

def objSuccIso :
    obj F X ⟨Order.succ j, by simp⟩ ≅ X :=
  eqToIso (dif_neg (by simpa only [Order.succ_le_iff_isMax] using hj))

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
    dif_pos (by rfl), map_id, comp_id, id_comp]

@[simp]
lemma map_id (i : J) (hi : i ≤ Order.succ j) :
    map hj F τ i i (by rfl) hi = 𝟙 _ := by
  dsimp [map]
  by_cases h₁ : i ≤ j
  · rw [dif_pos h₁, CategoryTheory.Functor.map_id, id_comp, Iso.hom_inv_id]
  · obtain rfl : i = Order.succ j := le_antisymm hi (Order.succ_le_of_lt (not_le.1 h₁))
    rw [dif_neg (by simpa only [Order.succ_le_iff_isMax] using hj),
      dif_neg h₁]

lemma map_comp (i₁ i₂ i₃ : J) (h₁₂ : i₁ ≤ i₂) (h₂₃ : i₂ ≤ i₃) (h : i₃ ≤ Order.succ j) :
    map hj F τ i₁ i₃ (h₁₂.trans h₂₃) h =
      map hj F τ i₁ i₂ h₁₂ (h₂₃.trans h) ≫ map hj F τ i₂ i₃ h₂₃ h := by
  by_cases h₁ : i₃ ≤ j
  · rw [map_eq hj F τ i₁ i₂ _ (h₂₃.trans h₁), map_eq hj F τ i₂ i₃ _ h₁,
      map_eq hj F τ i₁ i₃ _ h₁, assoc, assoc, Iso.inv_hom_id_assoc, ← map_comp_assoc,
      homOfLE_comp]
  · obtain rfl : i₃ = Order.succ j := le_antisymm h (Order.succ_le_of_lt (not_le.1 h₁))
    obtain h₂ | rfl := h₂₃.lt_or_eq
    · rw [Order.lt_succ_iff_of_not_isMax hj] at h₂
      rw [map_eq hj F τ i₁ i₂ _ h₂]
      dsimp [map]
      rw [dif_neg h₁, dif_pos (h₁₂.trans h₂), dif_neg h₁, dif_pos h₂,
        assoc, assoc, Iso.inv_hom_id_assoc,comp_id, ← map_comp_assoc, homOfLE_comp]
    · rw [map_id, comp_id]

end extendToSucc

open extendToSucc in

include hj in

def extendToSucc : Set.Iic (Order.succ j) ⥤ C where
  obj := obj F X
  map {i₁ i₂} f := map hj F τ i₁ i₂ (leOfHom f) i₂.2
  map_id _ := extendToSucc.map_id _ F τ _ _
  map_comp {i₁ i₂ i₃} f g := extendToSucc.map_comp hj F τ i₁ i₂ i₃ (leOfHom f) (leOfHom g) i₃.2

def extendToSuccObjIso (i : Set.Iic j) :
    (extendToSucc hj F τ).obj ⟨i, i.2.trans (Order.le_succ j)⟩ ≅ F.obj i :=
  extendToSucc.objIso F X i

def extendToSuccObjSuccIso :
    (extendToSucc hj F τ).obj ⟨Order.succ j, by simp⟩ ≅ X :=
  extendToSucc.objSuccIso hj F X

@[reassoc]
lemma extendToSuccObjIso_hom_naturality (i₁ i₂ : J) (hi : i₁ ≤ i₂) (hi₂ : i₂ ≤ j) :
    (extendToSucc hj F τ).map (homOfLE hi :
      ⟨i₁, hi.trans (hi₂.trans (Order.le_succ j))⟩ ⟶ ⟨i₂, hi₂.trans (Order.le_succ j)⟩) ≫
    (extendToSuccObjIso hj F τ ⟨i₂, hi₂⟩).hom =
      (extendToSuccObjIso hj F τ ⟨i₁, hi.trans hi₂⟩).hom ≫ F.map (homOfLE hi) := by
  dsimp [extendToSucc, extendToSuccObjIso]
  rw [extendToSucc.map_eq _ _ _ _ _ _ hi₂, assoc, assoc, Iso.inv_hom_id, comp_id]

@[simps!]
def extendToSuccRestrictionLEIso :
    Iteration.restrictionLE (extendToSucc hj F τ) (Order.le_succ j) ≅ F :=
  NatIso.ofComponents (extendToSuccObjIso hj F τ) (by
    rintro ⟨i₁, h₁⟩ ⟨i₂, h₂⟩ f
    apply extendToSuccObjIso_hom_naturality)

lemma extentToSucc_map (i₁ i₂ : J) (hi : i₁ ≤ i₂) (hi₂ : i₂ ≤ j) :
    (extendToSucc hj F τ).map (homOfLE hi :
      ⟨i₁, hi.trans (hi₂.trans (Order.le_succ j))⟩ ⟶ ⟨i₂, hi₂.trans (Order.le_succ j)⟩) =
      (extendToSuccObjIso hj F τ ⟨i₁, hi.trans hi₂⟩).hom ≫ F.map (homOfLE hi) ≫
      (extendToSuccObjIso hj F τ ⟨i₂, hi₂⟩).inv := by
  rw [← extendToSuccObjIso_hom_naturality_assoc, Iso.hom_inv_id, comp_id]

lemma extendToSucc_map_le_succ :
    (extendToSucc hj F τ).map (homOfLE (Order.le_succ j)) =
        (extendToSuccObjIso hj F τ ⟨j, by simp⟩).hom ≫ τ ≫
          (extendToSuccObjSuccIso hj F τ).inv :=
  extendToSucc.map_self_succ _ _ _

end Functor

end CategoryTheory
