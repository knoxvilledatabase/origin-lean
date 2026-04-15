/-
Extracted from CategoryTheory/EssentialImage.lean
Genuine: 17 of 26 | Dissolved: 0 | Infrastructure: 9
-/
import Origin.Core
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.FullSubcategory

/-!
# Essential image of a functor

The essential image `essImage` of a functor consists of the objects in the target category which
are isomorphic to an object in the image of the object function.
This, for instance, allows us to talk about objects belonging to a subcategory expressed as a
functor rather than a subtype, preserving the principle of equivalence. For example this lets us
define exponential ideals.

The essential image can also be seen as a subcategory of the target category, and witnesses that
a functor decomposes into an essentially surjective functor and a fully faithful functor.
(TODO: show that this decomposition forms an orthogonal factorisation system).
-/

universe v₁ v₂ v₃ u₁ u₂ u₃

noncomputable section

namespace CategoryTheory

variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] {F : C ⥤ D}

namespace Functor

def essImage (F : C ⥤ D) : Set D := fun Y => ∃ X : C, Nonempty (F.obj X ≅ Y)

def essImage.witness {Y : D} (h : Y ∈ F.essImage) : C :=
  h.choose

def essImage.getIso {Y : D} (h : Y ∈ F.essImage) : F.obj (essImage.witness h) ≅ Y :=
  Classical.choice h.choose_spec

theorem essImage.ofIso {Y Y' : D} (h : Y ≅ Y') (hY : Y ∈ essImage F) : Y' ∈ essImage F :=
  hY.imp fun _ => Nonempty.map (· ≪≫ h)

theorem essImage.ofNatIso {F' : C ⥤ D} (h : F ≅ F') {Y : D} (hY : Y ∈ essImage F) :
    Y ∈ essImage F' :=
  hY.imp fun X => Nonempty.map fun t => h.symm.app X ≪≫ t

theorem essImage_eq_of_natIso {F' : C ⥤ D} (h : F ≅ F') : essImage F = essImage F' :=
  funext fun _ => propext ⟨essImage.ofNatIso h, essImage.ofNatIso h.symm⟩

theorem obj_mem_essImage (F : D ⥤ C) (Y : D) : F.obj Y ∈ essImage F :=
  ⟨Y, ⟨Iso.refl _⟩⟩

def EssImageSubcategory (F : C ⥤ D) :=
  FullSubcategory F.essImage

instance : Category (EssImageSubcategory F) :=
  (inferInstance : Category.{v₂} (FullSubcategory _))

@[simps!]
def essImageInclusion (F : C ⥤ D) : F.EssImageSubcategory ⥤ D :=
  fullSubcategoryInclusion _

instance : Full (essImageInclusion F) :=
  (inferInstance : Full (fullSubcategoryInclusion _))

instance : Faithful (essImageInclusion F) :=
  (inferInstance : Faithful (fullSubcategoryInclusion _))

lemma essImage_ext (F : C ⥤ D) {X Y : F.EssImageSubcategory} (f g : X ⟶ Y)
    (h : F.essImageInclusion.map f = F.essImageInclusion.map g) : f = g := by
  simpa using h

@[simps!]
def toEssImage (F : C ⥤ D) : C ⥤ F.EssImageSubcategory :=
  FullSubcategory.lift _ F (obj_mem_essImage _)

@[simps!]
def toEssImageCompEssentialImageInclusion (F : C ⥤ D) : F.toEssImage ⋙ F.essImageInclusion ≅ F :=
  FullSubcategory.lift_comp_inclusion _ _ _

class EssSurj (F : C ⥤ D) : Prop where
  /-- All the objects of the target category are in the essential image. -/
  mem_essImage (Y : D) : Y ∈ F.essImage

instance EssSurj.toEssImage : EssSurj F.toEssImage where
  mem_essImage := fun ⟨_, hY⟩ =>
    ⟨_, ⟨⟨_, _, hY.getIso.hom_inv_id, hY.getIso.inv_hom_id⟩⟩⟩

theorem essSurj_of_surj (h : Function.Surjective F.obj) : EssSurj F where
  mem_essImage Y := by
    obtain ⟨X, rfl⟩ := h Y
    apply obj_mem_essImage

variable (F)

variable [F.EssSurj]

def objPreimage (Y : D) : C :=
  essImage.witness (@EssSurj.mem_essImage _ _ _ _ F _ Y)

def objObjPreimageIso (Y : D) : F.obj (F.objPreimage Y) ≅ Y :=
  Functor.essImage.getIso _

instance Faithful.toEssImage (F : C ⥤ D) [Faithful F] : Faithful F.toEssImage :=
  Faithful.of_comp_iso F.toEssImageCompEssentialImageInclusion

instance Full.toEssImage (F : C ⥤ D) [Full F] : Full F.toEssImage :=
  Full.of_comp_faithful_iso F.toEssImageCompEssentialImageInclusion

instance instEssSurjId : EssSurj (𝟭 C) where
  mem_essImage Y := ⟨Y, ⟨Iso.refl _⟩⟩

lemma essSurj_of_iso {F G : C ⥤ D} [EssSurj F] (α : F ≅ G) : EssSurj G where
  mem_essImage Y := Functor.essImage.ofNatIso α (EssSurj.mem_essImage Y)

instance essSurj_comp (F : C ⥤ D) (G : D ⥤ E) [F.EssSurj] [G.EssSurj] :
    (F ⋙ G).EssSurj where
  mem_essImage Z := ⟨_, ⟨G.mapIso (F.objObjPreimageIso _) ≪≫ G.objObjPreimageIso Z⟩⟩

lemma essSurj_of_comp_fully_faithful (F : C ⥤ D) (G : D ⥤ E) [(F ⋙ G).EssSurj]
    [G.Faithful] [G.Full] : F.EssSurj where
  mem_essImage X := ⟨_, ⟨G.preimageIso ((F ⋙ G).objObjPreimageIso (G.obj X))⟩⟩

end Functor

end CategoryTheory
