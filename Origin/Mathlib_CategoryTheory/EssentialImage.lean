/-
Extracted from CategoryTheory/EssentialImage.lean
Genuine: 9 of 10 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

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
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] {F : C ⥤ D} {G : D ⥤ E}

namespace Functor

def essImage (F : C ⥤ D) : ObjectProperty D := fun Y => ∃ X : C, Nonempty (F.obj X ≅ Y)

def essImage.witness {Y : D} (h : F.essImage Y) : C :=
  h.choose

def essImage.getIso {Y : D} (h : F.essImage Y) : F.obj h.witness ≅ Y :=
  Classical.choice h.choose_spec

theorem essImage.ofIso {Y Y' : D} (h : Y ≅ Y') (hY : essImage F Y) : essImage F Y' :=
  hY.imp fun _ => Nonempty.map (· ≪≫ h)

-- INSTANCE (free from Core): :

theorem essImage.ofNatIso {F' : C ⥤ D} (h : F ≅ F') {Y : D} (hY : essImage F Y) :
    essImage F' Y :=
  hY.imp fun X => Nonempty.map fun t => h.symm.app X ≪≫ t

theorem essImage_eq_of_natIso {F' : C ⥤ D} (h : F ≅ F') : essImage F = essImage F' :=
  funext fun _ => propext ⟨essImage.ofNatIso h, essImage.ofNatIso h.symm⟩

theorem obj_mem_essImage (F : D ⥤ C) (Y : D) : essImage F (F.obj Y) :=
  ⟨Y, ⟨Iso.refl _⟩⟩

abbrev EssImageSubcategory (F : C ⥤ D) := F.essImage.FullSubcategory

lemma essImage_ext (F : C ⥤ D) {X Y : F.EssImageSubcategory} (f g : X ⟶ Y)
    (h : F.essImage.ι.map f = F.essImage.ι.map g) : f = g :=
  F.essImage.ι.map_injective h
