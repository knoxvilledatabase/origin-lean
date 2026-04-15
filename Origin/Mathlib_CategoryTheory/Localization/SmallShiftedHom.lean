/-
Extracted from CategoryTheory/Localization/SmallShiftedHom.lean
Genuine: 17 of 22 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-!
# Shrinking morphisms in localized categories equipped with shifts

If `C` is a category equipped with a shift by an additive monoid `M`,
and `W : MorphismProperty C` is compatible with the shift,
we define a type-class `HasSmallLocalizedShiftedHom.{w} W X Y` which
says that all the types of morphisms from `X⟦a⟧` to `Y⟦b⟧` in the
localized category are `w`-small for a certain universe. Then,
we define types `SmallShiftedHom.{w} W X Y m : Type w` for all `m : M`,
and endow these with a composition which transports the composition
on the types `ShiftedHom (L.obj X) (L.obj Y) m` when `L : C ⥤ D` is
any localization functor for `W`.

-/

universe w'' w w' v₁ v₂ v₁' v₂' u₁ u₂ u₁' u₂'

namespace CategoryTheory

open Category

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (W : MorphismProperty C) {M : Type w'} [AddMonoid M] [HasShift C M] [HasShift D M]

namespace Localization

variable (X Y : C)

variable (M)

abbrev HasSmallLocalizedShiftedHom : Prop :=
  ∀ (a b : M), HasSmallLocalizedHom.{w} W (X⟦a⟧) (Y⟦b⟧)

lemma hasSmallLocalizedShiftedHom_iff
    (L : C ⥤ D) [L.IsLocalization W] [L.CommShift M] (X Y : C) :
    HasSmallLocalizedShiftedHom.{w} W M X Y ↔
      ∀ (a b : M), Small.{w} ((L.obj X)⟦a⟧ ⟶ (L.obj Y)⟦b⟧) := by
  dsimp [HasSmallLocalizedShiftedHom]
  have eq := fun (a b : M) ↦ small_congr.{w}
    (Iso.homCongr ((L.commShiftIso a).app X) ((L.commShiftIso b).app Y))
  dsimp at eq
  simp only [hasSmallLocalizedHom_iff _ L, eq]

variable {Y} in

lemma hasSmallLocalizedShiftedHom_iff_target [W.IsCompatibleWithShift M]
    {Y' : C} (f : Y ⟶ Y') (hf : W f) :
    HasSmallLocalizedShiftedHom.{w} W M X Y ↔ HasSmallLocalizedShiftedHom.{w} W M X Y' :=
  forall_congr' (fun a ↦ forall_congr' (fun b ↦
    hasSmallLocalizedHom_iff_target W (X⟦a⟧) (f⟦b⟧') (W.shift hf b)))

variable {X} in

lemma hasSmallLocalizedShiftedHom_iff_source [W.IsCompatibleWithShift M]
    {X' : C} (f : X ⟶ X') (hf : W f) (Y : C) :
    HasSmallLocalizedShiftedHom.{w} W M X Y ↔ HasSmallLocalizedShiftedHom.{w} W M X' Y :=
  forall_congr' (fun a ↦ forall_congr' (fun b ↦
    hasSmallLocalizedHom_iff_source W (f⟦a⟧') (W.shift hf a) (Y⟦b⟧)))

variable [HasSmallLocalizedShiftedHom.{w} W M X Y]

include M in

lemma hasSmallLocalizedHom_of_hasSmallLocalizedShiftedHom₀ :
    HasSmallLocalizedHom.{w} W X Y :=
  (hasSmallLocalizedHom_iff_of_isos W
    ((shiftFunctorZero C M).app X) ((shiftFunctorZero C M).app Y)).1 inferInstance

variable {M}

-- INSTANCE (free from Core): (m

-- INSTANCE (free from Core): (m

-- INSTANCE (free from Core): (m

-- INSTANCE (free from Core): (m

end

namespace SmallHom

variable {W}

variable [W.IsCompatibleWithShift M] (L : C ⥤ D) [L.IsLocalization W] [L.CommShift M]
  {X Y : C} [HasSmallLocalizedHom.{w} W X Y]
  (f : SmallHom.{w} W X Y) (a : M) [HasSmallLocalizedHom.{w} W (X⟦a⟧) (Y⟦a⟧)]

noncomputable def shift : SmallHom.{w} W (X⟦a⟧) (Y⟦a⟧) :=
  (W.shiftLocalizerMorphism a).smallHomMap f

lemma equiv_shift : equiv W L (f.shift a) =
    (L.commShiftIso a).hom.app X ≫ (equiv W L f)⟦a⟧' ≫ (L.commShiftIso a).inv.app Y :=
  (W.shiftLocalizerMorphism a).equiv_smallHomMap _ _ _ (L.commShiftIso a) f

end SmallHom

def SmallShiftedHom (X Y : C) [HasSmallLocalizedShiftedHom.{w} W M X Y] (m : M) : Type w :=
  SmallHom W X (Y⟦m⟧)

namespace SmallShiftedHom

variable [W.IsCompatibleWithShift M] {X Y Z : C}

noncomputable def mk {m : M} [HasSmallLocalizedShiftedHom.{w} W M X Y] (f : ShiftedHom X Y m) :
    SmallShiftedHom.{w} W X Y m :=
  SmallHom.mk _ f

variable {W}

noncomputable def shift {a : M} [HasSmallLocalizedShiftedHom.{w} W M X Y]
    [HasSmallLocalizedShiftedHom.{w} W M Y Y]
    (f : SmallShiftedHom.{w} W X Y a) (n a' : M) (h : a + n = a') :
    SmallHom.{w} W (X⟦n⟧) (Y⟦a'⟧) :=
  (SmallHom.shift f n).comp (SmallHom.mk W ((shiftFunctorAdd' C a n a' h).inv.app Y))

noncomputable def comp {a b c : M} [HasSmallLocalizedShiftedHom.{w} W M X Y]
    [HasSmallLocalizedShiftedHom.{w} W M Y Z] [HasSmallLocalizedShiftedHom.{w} W M X Z]
    [HasSmallLocalizedShiftedHom.{w} W M Z Z]
    (f : SmallShiftedHom.{w} W X Y a) (g : SmallShiftedHom.{w} W Y Z b) (h : b + a = c) :
    SmallShiftedHom.{w} W X Z c :=
  SmallHom.comp f (g.shift a c h)

variable (W) in

noncomputable def mk₀ [HasSmallLocalizedShiftedHom.{w} W M X Y]
    (m₀ : M) (hm₀ : m₀ = 0) (f : X ⟶ Y) :
    SmallShiftedHom.{w} W X Y m₀ :=
  SmallShiftedHom.mk _ (ShiftedHom.mk₀ _ hm₀ f)

noncomputable def mk₀Inv [HasSmallLocalizedShiftedHom.{w} W M Y X] [W.RespectsIso]
    (m₀ : M) (hm₀ : m₀ = 0) (f : X ⟶ Y) (hf : W f) :
    SmallShiftedHom.{w} W Y X m₀ :=
  SmallHom.mkInv ((shiftFunctorZero' C m₀ hm₀).hom.app X ≫ f)
    (MorphismProperty.RespectsIso.precomp _ _ _ hf)

end

variable (L : C ⥤ D) [L.IsLocalization W] [L.CommShift M]
  {X Y Z T : C}

noncomputable def equiv [HasSmallLocalizedShiftedHom.{w} W M X Y] {m : M} :
    SmallShiftedHom.{w} W X Y m ≃ ShiftedHom (L.obj X) (L.obj Y) m :=
  (SmallHom.equiv W L).trans ((L.commShiftIso m).app Y).homToEquiv

variable [W.IsCompatibleWithShift M]

set_option backward.isDefEq.respectTransparency false in

lemma equiv_shift' {a : M} [HasSmallLocalizedShiftedHom.{w} W M X Y]
    [HasSmallLocalizedShiftedHom.{w} W M Y Y]
    (f : SmallShiftedHom.{w} W X Y a) (n a' : M) (h : a + n = a') :
    SmallHom.equiv W L (f.shift n a' h) = (L.commShiftIso n).hom.app X ≫
      (SmallHom.equiv W L f)⟦n⟧' ≫ ((L.commShiftIso a).hom.app Y)⟦n⟧' ≫
        (shiftFunctorAdd' D a n a' h).inv.app (L.obj Y) ≫ (L.commShiftIso a').inv.app Y := by
  simp only [shift, SmallHom.equiv_comp, SmallHom.equiv_shift, SmallHom.equiv_mk, assoc,
    L.commShiftIso_add' h, Functor.CommShift.isoAdd'_inv_app, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app, Functor.comp_obj, comp_id]

set_option backward.isDefEq.respectTransparency false in

lemma equiv_shift {a : M} [HasSmallLocalizedShiftedHom.{w} W M X Y]
    [HasSmallLocalizedShiftedHom.{w} W M Y Y]
    (f : SmallShiftedHom.{w} W X Y a) (n a' : M) (h : a + n = a') :
    equiv W L (f.shift n a' h) = (L.commShiftIso n).hom.app X ≫ (equiv W L f)⟦n⟧' ≫
      (shiftFunctorAdd' D a n a' h).inv.app (L.obj Y) := by
  dsimp [equiv]
  erw [equiv_shift']
  simp only [Functor.comp_obj, assoc, Iso.inv_hom_id_app, comp_id, Functor.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in

lemma equiv_comp [HasSmallLocalizedShiftedHom.{w} W M X Y]
    [HasSmallLocalizedShiftedHom.{w} W M Y Z] [HasSmallLocalizedShiftedHom.{w} W M X Z]
    [HasSmallLocalizedShiftedHom.{w} W M Z Z] {a b c : M}
    (f : SmallShiftedHom.{w} W X Y a) (g : SmallShiftedHom.{w} W Y Z b) (h : b + a = c) :
    equiv W L (f.comp g h) = (equiv W L f).comp (equiv W L g) h := by
  dsimp [comp, equiv, ShiftedHom.comp]
  erw [SmallHom.equiv_comp]
  simp only [equiv_shift', Functor.comp_obj, assoc, Iso.inv_hom_id_app,
    comp_id, Functor.map_comp]
  rfl

end

set_option backward.isDefEq.respectTransparency false in
