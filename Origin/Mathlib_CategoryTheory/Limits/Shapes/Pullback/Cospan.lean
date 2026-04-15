/-
Extracted from CategoryTheory/Limits/Shapes/Pullback/Cospan.lean
Genuine: 44 | Conflates: 0 | Dissolved: 0 | Infrastructure: 32
-/
import Origin.Core
import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

/-!
# Cospan & Span

We define a category `WalkingCospan` (resp. `WalkingSpan`), which is the index category
for the given data for a pullback (resp. pushout) diagram. Convenience methods `cospan f g`
and `span f g` construct functors from the walking (co)span, hitting the given morphisms.

## References
* [Stacks: Fibre products](https://stacks.math.columbia.edu/tag/001U)
* [Stacks: Pushouts](https://stacks.math.columbia.edu/tag/0025)
-/

noncomputable section

open CategoryTheory

universe w v₁ v₂ v u u₂

namespace CategoryTheory.Limits

abbrev WalkingCospan : Type :=
  WidePullbackShape WalkingPair

@[match_pattern]
abbrev WalkingCospan.left : WalkingCospan :=
  some WalkingPair.left

@[match_pattern]
abbrev WalkingCospan.right : WalkingCospan :=
  some WalkingPair.right

@[match_pattern]
abbrev WalkingCospan.one : WalkingCospan :=
  none

abbrev WalkingSpan : Type :=
  WidePushoutShape WalkingPair

@[match_pattern]
abbrev WalkingSpan.left : WalkingSpan :=
  some WalkingPair.left

@[match_pattern]
abbrev WalkingSpan.right : WalkingSpan :=
  some WalkingPair.right

@[match_pattern]
abbrev WalkingSpan.zero : WalkingSpan :=
  none

namespace WalkingCospan

abbrev Hom : WalkingCospan → WalkingCospan → Type :=
  WidePullbackShape.Hom

@[match_pattern]
abbrev Hom.inl : left ⟶ one :=
  WidePullbackShape.Hom.term _

@[match_pattern]
abbrev Hom.inr : right ⟶ one :=
  WidePullbackShape.Hom.term _

@[match_pattern]
abbrev Hom.id (X : WalkingCospan) : X ⟶ X :=
  WidePullbackShape.Hom.id X

instance (X Y : WalkingCospan) : Subsingleton (X ⟶ Y) := by
  constructor; intros; simp [eq_iff_true_of_subsingleton]

end WalkingCospan

namespace WalkingSpan

abbrev Hom : WalkingSpan → WalkingSpan → Type :=
  WidePushoutShape.Hom

@[match_pattern]
abbrev Hom.fst : zero ⟶ left :=
  WidePushoutShape.Hom.init _

@[match_pattern]
abbrev Hom.snd : zero ⟶ right :=
  WidePushoutShape.Hom.init _

@[match_pattern]
abbrev Hom.id (X : WalkingSpan) : X ⟶ X :=
  WidePushoutShape.Hom.id X

instance (X Y : WalkingSpan) : Subsingleton (X ⟶ Y) := by
  constructor; intros a b; simp [eq_iff_true_of_subsingleton]

end WalkingSpan

open WalkingSpan.Hom WalkingCospan.Hom WidePullbackShape.Hom WidePushoutShape.Hom

variable {C : Type u} [Category.{v} C]

def WalkingCospan.ext {F : WalkingCospan ⥤ C} {s t : Cone F} (i : s.pt ≅ t.pt)
    (w₁ : s.π.app WalkingCospan.left = i.hom ≫ t.π.app WalkingCospan.left)
    (w₂ : s.π.app WalkingCospan.right = i.hom ≫ t.π.app WalkingCospan.right) : s ≅ t := by
  apply Cones.ext i _
  rintro (⟨⟩ | ⟨⟨⟩⟩)
  · have h₁ := s.π.naturality WalkingCospan.Hom.inl
    dsimp at h₁
    simp only [Category.id_comp] at h₁
    have h₂ := t.π.naturality WalkingCospan.Hom.inl
    dsimp at h₂
    simp only [Category.id_comp] at h₂
    simp_rw [h₂, ← Category.assoc, ← w₁, ← h₁]
  · exact w₁
  · exact w₂

def WalkingSpan.ext {F : WalkingSpan ⥤ C} {s t : Cocone F} (i : s.pt ≅ t.pt)
    (w₁ : s.ι.app WalkingCospan.left ≫ i.hom = t.ι.app WalkingCospan.left)
    (w₂ : s.ι.app WalkingCospan.right ≫ i.hom = t.ι.app WalkingCospan.right) : s ≅ t := by
  apply Cocones.ext i _
  rintro (⟨⟩ | ⟨⟨⟩⟩)
  · have h₁ := s.ι.naturality WalkingSpan.Hom.fst
    dsimp at h₁
    simp only [Category.comp_id] at h₁
    have h₂ := t.ι.naturality WalkingSpan.Hom.fst
    dsimp at h₂
    simp only [Category.comp_id] at h₂
    simp_rw [← h₁, Category.assoc, w₁, h₂]
  · exact w₁
  · exact w₂

def cospan {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : WalkingCospan ⥤ C :=
  WidePullbackShape.wideCospan Z (fun j => WalkingPair.casesOn j X Y) fun j =>
    WalkingPair.casesOn j f g

def span {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : WalkingSpan ⥤ C :=
  WidePushoutShape.wideSpan X (fun j => WalkingPair.casesOn j Y Z) fun j =>
    WalkingPair.casesOn j f g

@[simp]
theorem cospan_left {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : (cospan f g).obj WalkingCospan.left = X :=
  rfl

@[simp]
theorem span_left {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : (span f g).obj WalkingSpan.left = Y :=
  rfl

@[simp]
theorem cospan_right {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (cospan f g).obj WalkingCospan.right = Y := rfl

@[simp]
theorem span_right {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : (span f g).obj WalkingSpan.right = Z :=
  rfl

@[simp]
theorem cospan_one {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : (cospan f g).obj WalkingCospan.one = Z :=
  rfl

@[simp]
theorem span_zero {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : (span f g).obj WalkingSpan.zero = X :=
  rfl

@[simp]
theorem cospan_map_inl {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (cospan f g).map WalkingCospan.Hom.inl = f := rfl

@[simp]
theorem span_map_fst {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : (span f g).map WalkingSpan.Hom.fst = f :=
  rfl

@[simp]
theorem cospan_map_inr {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (cospan f g).map WalkingCospan.Hom.inr = g := rfl

@[simp]
theorem span_map_snd {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : (span f g).map WalkingSpan.Hom.snd = g :=
  rfl

theorem cospan_map_id {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (w : WalkingCospan) :
    (cospan f g).map (WalkingCospan.Hom.id w) = 𝟙 _ := rfl

theorem span_map_id {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) (w : WalkingSpan) :
    (span f g).map (WalkingSpan.Hom.id w) = 𝟙 _ := rfl

@[simps!]
def diagramIsoCospan (F : WalkingCospan ⥤ C) : F ≅ cospan (F.map inl) (F.map inr) :=
  NatIso.ofComponents
  (fun j => eqToIso (by rcases j with (⟨⟩ | ⟨⟨⟩⟩) <;> rfl))
  (by rintro (⟨⟩ | ⟨⟨⟩⟩) (⟨⟩ | ⟨⟨⟩⟩) f <;> cases f <;> dsimp <;> simp)

@[simps!]
def diagramIsoSpan (F : WalkingSpan ⥤ C) : F ≅ span (F.map fst) (F.map snd) :=
  NatIso.ofComponents
  (fun j => eqToIso (by rcases j with (⟨⟩ | ⟨⟨⟩⟩) <;> rfl))
  (by rintro (⟨⟩ | ⟨⟨⟩⟩) (⟨⟩ | ⟨⟨⟩⟩) f <;> cases f <;> dsimp <;> simp)

variable {D : Type u₂} [Category.{v₂} D]

def cospanCompIso (F : C ⥤ D) {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    cospan f g ⋙ F ≅ cospan (F.map f) (F.map g) :=
  NatIso.ofComponents (by rintro (⟨⟩ | ⟨⟨⟩⟩) <;> exact Iso.refl _)
    (by rintro (⟨⟩ | ⟨⟨⟩⟩) (⟨⟩ | ⟨⟨⟩⟩) f <;> cases f <;> dsimp <;> simp)

section

variable (F : C ⥤ D) {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)

@[simp]
theorem cospanCompIso_app_left : (cospanCompIso F f g).app WalkingCospan.left = Iso.refl _ := rfl

@[simp]
theorem cospanCompIso_app_right : (cospanCompIso F f g).app WalkingCospan.right = Iso.refl _ :=
  rfl

@[simp]
theorem cospanCompIso_app_one : (cospanCompIso F f g).app WalkingCospan.one = Iso.refl _ := rfl

@[simp]
theorem cospanCompIso_hom_app_left : (cospanCompIso F f g).hom.app WalkingCospan.left = 𝟙 _ :=
  rfl

@[simp]
theorem cospanCompIso_hom_app_right : (cospanCompIso F f g).hom.app WalkingCospan.right = 𝟙 _ :=
  rfl

@[simp]
theorem cospanCompIso_hom_app_one : (cospanCompIso F f g).hom.app WalkingCospan.one = 𝟙 _ := rfl

@[simp]
theorem cospanCompIso_inv_app_left : (cospanCompIso F f g).inv.app WalkingCospan.left = 𝟙 _ :=
  rfl

@[simp]
theorem cospanCompIso_inv_app_right : (cospanCompIso F f g).inv.app WalkingCospan.right = 𝟙 _ :=
  rfl

@[simp]
theorem cospanCompIso_inv_app_one : (cospanCompIso F f g).inv.app WalkingCospan.one = 𝟙 _ := rfl

end

def spanCompIso (F : C ⥤ D) {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :
    span f g ⋙ F ≅ span (F.map f) (F.map g) :=
  NatIso.ofComponents (by rintro (⟨⟩ | ⟨⟨⟩⟩) <;> exact Iso.refl _)
    (by rintro (⟨⟩ | ⟨⟨⟩⟩) (⟨⟩ | ⟨⟨⟩⟩) f <;> cases f <;> dsimp <;> simp)

section

variable (F : C ⥤ D) {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)

@[simp]
theorem spanCompIso_app_left : (spanCompIso F f g).app WalkingSpan.left = Iso.refl _ := rfl

@[simp]
theorem spanCompIso_app_right : (spanCompIso F f g).app WalkingSpan.right = Iso.refl _ := rfl

@[simp]
theorem spanCompIso_app_zero : (spanCompIso F f g).app WalkingSpan.zero = Iso.refl _ := rfl

@[simp]
theorem spanCompIso_hom_app_left : (spanCompIso F f g).hom.app WalkingSpan.left = 𝟙 _ := rfl

@[simp]
theorem spanCompIso_hom_app_right : (spanCompIso F f g).hom.app WalkingSpan.right = 𝟙 _ := rfl

@[simp]
theorem spanCompIso_hom_app_zero : (spanCompIso F f g).hom.app WalkingSpan.zero = 𝟙 _ := rfl

@[simp]
theorem spanCompIso_inv_app_left : (spanCompIso F f g).inv.app WalkingSpan.left = 𝟙 _ := rfl

@[simp]
theorem spanCompIso_inv_app_right : (spanCompIso F f g).inv.app WalkingSpan.right = 𝟙 _ := rfl

@[simp]
theorem spanCompIso_inv_app_zero : (spanCompIso F f g).inv.app WalkingSpan.zero = 𝟙 _ := rfl

end

section

variable {X Y Z X' Y' Z' : C} (iX : X ≅ X') (iY : Y ≅ Y') (iZ : Z ≅ Z')

section

variable {f : X ⟶ Z} {g : Y ⟶ Z} {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'}

def cospanExt (wf : iX.hom ≫ f' = f ≫ iZ.hom) (wg : iY.hom ≫ g' = g ≫ iZ.hom) :
    cospan f g ≅ cospan f' g' :=
  NatIso.ofComponents
    (by rintro (⟨⟩ | ⟨⟨⟩⟩); exacts [iZ, iX, iY])
    (by rintro (⟨⟩ | ⟨⟨⟩⟩) (⟨⟩ | ⟨⟨⟩⟩) f <;> cases f <;> dsimp <;> simp [wf, wg])

variable (wf : iX.hom ≫ f' = f ≫ iZ.hom) (wg : iY.hom ≫ g' = g ≫ iZ.hom)

@[simp]
theorem cospanExt_app_left : (cospanExt iX iY iZ wf wg).app WalkingCospan.left = iX := by
  dsimp [cospanExt]

@[simp]
theorem cospanExt_app_right : (cospanExt iX iY iZ wf wg).app WalkingCospan.right = iY := by
  dsimp [cospanExt]

@[simp]
theorem cospanExt_app_one : (cospanExt iX iY iZ wf wg).app WalkingCospan.one = iZ := by
  dsimp [cospanExt]

@[simp]
theorem cospanExt_hom_app_left :
    (cospanExt iX iY iZ wf wg).hom.app WalkingCospan.left = iX.hom := by dsimp [cospanExt]

@[simp]
theorem cospanExt_hom_app_right :
    (cospanExt iX iY iZ wf wg).hom.app WalkingCospan.right = iY.hom := by dsimp [cospanExt]

@[simp]
theorem cospanExt_hom_app_one : (cospanExt iX iY iZ wf wg).hom.app WalkingCospan.one = iZ.hom := by
  dsimp [cospanExt]

@[simp]
theorem cospanExt_inv_app_left :
    (cospanExt iX iY iZ wf wg).inv.app WalkingCospan.left = iX.inv := by dsimp [cospanExt]

@[simp]
theorem cospanExt_inv_app_right :
    (cospanExt iX iY iZ wf wg).inv.app WalkingCospan.right = iY.inv := by dsimp [cospanExt]

@[simp]
theorem cospanExt_inv_app_one : (cospanExt iX iY iZ wf wg).inv.app WalkingCospan.one = iZ.inv := by
  dsimp [cospanExt]

end

section

variable {f : X ⟶ Y} {g : X ⟶ Z} {f' : X' ⟶ Y'} {g' : X' ⟶ Z'}

def spanExt (wf : iX.hom ≫ f' = f ≫ iY.hom) (wg : iX.hom ≫ g' = g ≫ iZ.hom) :
    span f g ≅ span f' g' :=
  NatIso.ofComponents (by rintro (⟨⟩ | ⟨⟨⟩⟩); exacts [iX, iY, iZ])
    (by rintro (⟨⟩ | ⟨⟨⟩⟩) (⟨⟩ | ⟨⟨⟩⟩) f <;> cases f <;> dsimp <;> simp [wf, wg])

variable (wf : iX.hom ≫ f' = f ≫ iY.hom) (wg : iX.hom ≫ g' = g ≫ iZ.hom)

@[simp]
theorem spanExt_app_left : (spanExt iX iY iZ wf wg).app WalkingSpan.left = iY := by
  dsimp [spanExt]

@[simp]
theorem spanExt_app_right : (spanExt iX iY iZ wf wg).app WalkingSpan.right = iZ := by
  dsimp [spanExt]

@[simp]
theorem spanExt_app_one : (spanExt iX iY iZ wf wg).app WalkingSpan.zero = iX := by
  dsimp [spanExt]

@[simp]
theorem spanExt_hom_app_left : (spanExt iX iY iZ wf wg).hom.app WalkingSpan.left = iY.hom := by
  dsimp [spanExt]

@[simp]
theorem spanExt_hom_app_right : (spanExt iX iY iZ wf wg).hom.app WalkingSpan.right = iZ.hom := by
  dsimp [spanExt]

@[simp]
theorem spanExt_hom_app_zero : (spanExt iX iY iZ wf wg).hom.app WalkingSpan.zero = iX.hom := by
  dsimp [spanExt]

@[simp]
theorem spanExt_inv_app_left : (spanExt iX iY iZ wf wg).inv.app WalkingSpan.left = iY.inv := by
  dsimp [spanExt]

@[simp]
theorem spanExt_inv_app_right : (spanExt iX iY iZ wf wg).inv.app WalkingSpan.right = iZ.inv := by
  dsimp [spanExt]

@[simp]
theorem spanExt_inv_app_zero : (spanExt iX iY iZ wf wg).inv.app WalkingSpan.zero = iX.inv := by
  dsimp [spanExt]

end

end

end CategoryTheory.Limits
