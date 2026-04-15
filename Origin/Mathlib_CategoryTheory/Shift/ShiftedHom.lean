/-
Extracted from CategoryTheory/Shift/ShiftedHom.lean
Genuine: 22 | Conflates: 0 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core
import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! Shifted morphisms

Given a category `C` endowed with a shift by an additive monoid `M` and two
objects `X` and `Y` in `C`, we consider the types `ShiftedHom X Y m`
defined as `X ⟶ (Y⟦m⟧)` for all `m : M`, and the composition on these
shifted hom.

## TODO

* redefine Ext-groups in abelian categories using `ShiftedHom` in the derived category.
* study the `R`-module structures on `ShiftedHom` when `C` is `R`-linear

-/

namespace CategoryTheory

open Category

variable {C : Type*} [Category C] {D : Type*} [Category D] {E : Type*} [Category E]
  {M : Type*} [AddMonoid M] [HasShift C M] [HasShift D M] [HasShift E M]

def ShiftedHom (X Y : C) (m : M) : Type _ := X ⟶ (Y⟦m⟧)

instance [Preadditive C] (X Y : C) (n : M) : AddCommGroup (ShiftedHom X Y n) := by
  dsimp only [ShiftedHom]
  infer_instance

namespace ShiftedHom

variable {X Y Z T : C}

noncomputable def comp {a b c : M} (f : ShiftedHom X Y a) (g : ShiftedHom Y Z b) (h : b + a = c) :
    ShiftedHom X Z c :=
  f ≫ g⟦a⟧' ≫ (shiftFunctorAdd' C b a c h).inv.app _

lemma comp_assoc {a₁ a₂ a₃ a₁₂ a₂₃ a : M}
    (α : ShiftedHom X Y a₁) (β : ShiftedHom Y Z a₂) (γ : ShiftedHom Z T a₃)
    (h₁₂ : a₂ + a₁ = a₁₂) (h₂₃ : a₃ + a₂ = a₂₃) (h : a₃ + a₂ + a₁ = a) :
    (α.comp β h₁₂).comp γ (show a₃ + a₁₂ = a by rw [← h₁₂, ← add_assoc, h]) =
      α.comp (β.comp γ h₂₃) (by rw [← h₂₃, h]) := by
  simp only [comp, assoc, Functor.map_comp,
    shiftFunctorAdd'_assoc_inv_app a₃ a₂ a₁ a₂₃ a₁₂ a h₂₃ h₁₂ h,
    ← NatTrans.naturality_assoc, Functor.comp_map]

/-! In degree `0 : M`, shifted hom `ShiftedHom X Y 0` identify to morphisms `X ⟶ Y`.
We generalize this to `m₀ : M` such that `m₀ : 0` as it shall be convenient when we
apply this with `M := ℤ` and `m₀` the coercion of `0 : ℕ`. -/

noncomputable def mk₀ (m₀ : M) (hm₀ : m₀ = 0) (f : X ⟶ Y) : ShiftedHom X Y m₀ :=
  f ≫ (shiftFunctorZero' C m₀ hm₀).inv.app Y

@[simps apply]
noncomputable def homEquiv (m₀ : M) (hm₀ : m₀ = 0) : (X ⟶ Y) ≃ ShiftedHom X Y m₀ where
  toFun f := mk₀ m₀ hm₀ f
  invFun g := g ≫ (shiftFunctorZero' C m₀ hm₀).hom.app Y
  left_inv f := by simp [mk₀]
  right_inv g := by simp [mk₀]

lemma mk₀_comp (m₀ : M) (hm₀ : m₀ = 0) (f : X ⟶ Y) {a : M} (g : ShiftedHom Y Z a) :
    (mk₀ m₀ hm₀ f).comp g (by rw [hm₀, add_zero]) = f ≫ g := by
  subst hm₀
  simp [comp, mk₀, shiftFunctorAdd'_add_zero_inv_app, shiftFunctorZero']

@[simp]
lemma mk₀_id_comp (m₀ : M) (hm₀ : m₀ = 0) {a : M} (f : ShiftedHom X Y a) :
    (mk₀ m₀ hm₀ (𝟙 X)).comp f (by rw [hm₀, add_zero]) = f := by
  simp [mk₀_comp]

lemma comp_mk₀ {a : M} (f : ShiftedHom X Y a) (m₀ : M) (hm₀ : m₀ = 0) (g : Y ⟶ Z) :
    f.comp (mk₀ m₀ hm₀ g) (by rw [hm₀, zero_add]) = f ≫ g⟦a⟧' := by
  subst hm₀
  simp only [comp, shiftFunctorAdd'_zero_add_inv_app, mk₀, shiftFunctorZero',
    eqToIso_refl, Iso.refl_trans, ← Functor.map_comp, assoc, Iso.inv_hom_id_app,
    Functor.id_obj, comp_id]

@[simp]
lemma comp_mk₀_id {a : M} (f : ShiftedHom X Y a) (m₀ : M) (hm₀ : m₀ = 0) :
    f.comp (mk₀ m₀ hm₀ (𝟙 Y)) (by rw [hm₀, zero_add]) = f := by
  simp [comp_mk₀]

@[simp 1100]
lemma mk₀_comp_mk₀ (f : X ⟶ Y) (g : Y ⟶ Z) {a b c : M} (h : b + a = c)
    (ha : a = 0) (hb : b = 0) :
    (mk₀ a ha f).comp (mk₀ b hb g) h = mk₀ c (by rw [← h, ha, hb, add_zero]) (f ≫ g) := by
  subst ha hb
  obtain rfl : c = 0 := by rw [← h, zero_add]
  rw [mk₀_comp, mk₀, mk₀, assoc]

@[simp]
lemma mk₀_comp_mk₀_assoc (f : X ⟶ Y) (g : Y ⟶ Z) {a : M}
    (ha : a = 0) {d : M} (h : ShiftedHom Z T d) :
    (mk₀ a ha f).comp ((mk₀ a ha g).comp h
        (show _ = d by rw [ha, add_zero])) (show _ = d by rw [ha, add_zero]) =
      (mk₀ a ha (f ≫ g)).comp h (by rw [ha, add_zero]) := by
  subst ha
  rw [← comp_assoc, mk₀_comp_mk₀]
  all_goals simp

section Preadditive

variable [Preadditive C]

variable (X Y) in

@[simp]
lemma mk₀_zero (m₀ : M) (hm₀ : m₀ = 0) : mk₀ m₀ hm₀ (0 : X ⟶ Y) = 0 := by simp [mk₀]

@[simp]
lemma comp_add [∀ (a : M), (shiftFunctor C a).Additive]
    {a b c : M} (α : ShiftedHom X Y a) (β₁ β₂ : ShiftedHom Y Z b) (h : b + a = c) :
    α.comp (β₁ + β₂) h = α.comp β₁ h + α.comp β₂ h := by
  rw [comp, comp, comp, Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]

@[simp]
lemma add_comp
    {a b c : M} (α₁ α₂ : ShiftedHom X Y a) (β : ShiftedHom Y Z b) (h : b + a = c) :
    (α₁ + α₂).comp β h = α₁.comp β h + α₂.comp β h := by
  rw [comp, comp, comp, Preadditive.add_comp]

@[simp]
lemma comp_neg [∀ (a : M), (shiftFunctor C a).Additive]
    {a b c : M} (α : ShiftedHom X Y a) (β : ShiftedHom Y Z b) (h : b + a = c) :
    α.comp (-β) h = -α.comp β h := by
  rw [comp, comp, Functor.map_neg, Preadditive.neg_comp, Preadditive.comp_neg]

@[simp]
lemma neg_comp
    {a b c : M} (α : ShiftedHom X Y a) (β : ShiftedHom Y Z b) (h : b + a = c) :
    (-α).comp β h = -α.comp β h := by
  rw [comp, comp, Preadditive.neg_comp]

variable (Z) in

@[simp]
lemma comp_zero [∀ (a : M), (shiftFunctor C a).PreservesZeroMorphisms]
    {a : M} (β : ShiftedHom X Y a) {b c : M} (h : b + a = c) :
    β.comp (0 : ShiftedHom Y Z b) h = 0 := by
  rw [comp, Functor.map_zero, Limits.zero_comp, Limits.comp_zero]

variable (X) in

@[simp]
lemma zero_comp (a : M) {b c : M} (β : ShiftedHom Y Z b) (h : b + a = c) :
    (0 : ShiftedHom X Y a).comp β h = 0 := by
  rw [comp, Limits.zero_comp]

end Preadditive

def map {a : M} (f : ShiftedHom X Y a) (F : C ⥤ D) [F.CommShift M] :
    ShiftedHom (F.obj X) (F.obj Y) a :=
  F.map f ≫ (F.commShiftIso a).hom.app Y

@[simp]
lemma id_map {a : M} (f : ShiftedHom X Y a) : f.map (𝟭 C) = f := by
  simp [map, Functor.commShiftIso, Functor.CommShift.iso]

lemma comp_map {a : M} (f : ShiftedHom X Y a) (F : C ⥤ D) [F.CommShift M]
    (G : D ⥤ E) [G.CommShift M] : f.map (F ⋙ G) = (f.map F).map G := by
  simp [map, Functor.commShiftIso_comp_hom_app]

lemma map_comp {a b c : M} (f : ShiftedHom X Y a) (g : ShiftedHom Y Z b)
    (h : b + a = c) (F : C ⥤ D) [F.CommShift M] :
    (f.comp g h).map F = (f.map F).comp (g.map F) h := by
  dsimp [comp, map]
  simp only [Functor.map_comp, assoc]
  erw [← NatTrans.naturality_assoc]
  simp only [Functor.comp_map, F.commShiftIso_add' h, Functor.CommShift.isoAdd'_hom_app,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.comp_obj, comp_id, assoc]

end ShiftedHom

end CategoryTheory
