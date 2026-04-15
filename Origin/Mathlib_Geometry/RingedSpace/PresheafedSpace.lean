/-
Extracted from Geometry/RingedSpace/PresheafedSpace.lean
Genuine: 24 | Conflates: 0 | Dissolved: 0 | Infrastructure: 22
-/
import Origin.Core
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# Presheafed spaces

Introduces the category of topological spaces equipped with a presheaf (taking values in an
arbitrary target category `C`.)

We further describe how to apply functors and natural transformations to the values of the
presheaves.
-/

open Opposite CategoryTheory CategoryTheory.Category CategoryTheory.Functor TopCat TopologicalSpace

  Topology

variable (C : Type*) [Category C]

namespace AlgebraicGeometry

structure PresheafedSpace where
  carrier : TopCat
  protected presheaf : carrier.Presheaf C

variable {C}

namespace PresheafedSpace

instance coeCarrier : CoeOut (PresheafedSpace C) TopCat where coe X := X.carrier

attribute [coe] PresheafedSpace.carrier

instance : CoeSort (PresheafedSpace C) Type* where coe X := X.carrier

theorem mk_coe (carrier) (presheaf) :
    (({ carrier
        presheaf } : PresheafedSpace C) : TopCat) = carrier :=
  rfl

instance (X : PresheafedSpace C) : TopologicalSpace X :=
  X.carrier.str

def const (X : TopCat) (Z : C) : PresheafedSpace C where
  carrier := X
  presheaf := (Functor.const _).obj Z

instance [Inhabited C] : Inhabited (PresheafedSpace C) :=
  ⟨const (TopCat.of PEmpty) default⟩

structure Hom (X Y : PresheafedSpace C) where
  base : (X : TopCat) ⟶ (Y : TopCat)
  c : Y.presheaf ⟶ base _* X.presheaf

@[ext (iff := false)]
theorem Hom.ext {X Y : PresheafedSpace C} (α β : Hom X Y) (w : α.base = β.base)
    (h : α.c ≫ whiskerRight (eqToHom (by rw [w])) _ = β.c) : α = β := by
  rcases α with ⟨base, c⟩
  rcases β with ⟨base', c'⟩
  dsimp at w
  subst w
  dsimp at h
  erw [whiskerRight_id', comp_id] at h
  subst h
  rfl

theorem hext {X Y : PresheafedSpace C} (α β : Hom X Y) (w : α.base = β.base) (h : HEq α.c β.c) :
    α = β := by
  cases α
  cases β
  congr

def id (X : PresheafedSpace C) : Hom X X where
  base := 𝟙 (X : TopCat)
  c := 𝟙 _

instance homInhabited (X : PresheafedSpace C) : Inhabited (Hom X X) :=
  ⟨id X⟩

def comp {X Y Z : PresheafedSpace C} (α : Hom X Y) (β : Hom Y Z) : Hom X Z where
  base := α.base ≫ β.base
  c := β.c ≫ (Presheaf.pushforward _ β.base).map α.c

theorem comp_c {X Y Z : PresheafedSpace C} (α : Hom X Y) (β : Hom Y Z) :
    (comp α β).c = β.c ≫ (Presheaf.pushforward _ β.base).map α.c :=
  rfl

variable (C)

section

attribute [local simp] id comp

instance categoryOfPresheafedSpaces : Category (PresheafedSpace C) where
  Hom := Hom
  id := id
  comp := comp
  id_comp _ := by
    dsimp
    ext
    · dsimp
      simp
    · dsimp
      simp only [map_id, whiskerRight_id', assoc]
      erw [comp_id, comp_id]

variable {C}

abbrev Hom.toPshHom {X Y : PresheafedSpace C} (f : Hom X Y) : X ⟶ Y := f

@[ext (iff := false)]
theorem ext {X Y : PresheafedSpace C} (α β : X ⟶ Y) (w : α.base = β.base)
    (h : α.c ≫ whiskerRight (eqToHom (by rw [w])) _ = β.c) : α = β :=
  Hom.ext α β w h

end

variable {C}

attribute [local simp] eqToHom_map

@[simp]
theorem id_base (X : PresheafedSpace C) : (𝟙 X : X ⟶ X).base = 𝟙 (X : TopCat) :=
  rfl

theorem id_c (X : PresheafedSpace C) :
    (𝟙 X : X ⟶ X).c = 𝟙 X.presheaf :=
  rfl

@[simp]
theorem id_c_app (X : PresheafedSpace C) (U) :
    (𝟙 X : X ⟶ X).c.app U = X.presheaf.map (𝟙 U) := by
  rw [id_c, map_id]
  rfl

@[simp]
theorem comp_base {X Y Z : PresheafedSpace C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).base = f.base ≫ g.base :=
  rfl

instance (X Y : PresheafedSpace C) : CoeFun (X ⟶ Y) fun _ => (↑X → ↑Y) :=
  ⟨fun f => f.base⟩

@[reassoc, simp]
theorem comp_c_app {X Y Z : PresheafedSpace C} (α : X ⟶ Y) (β : Y ⟶ Z) (U) :
    (α ≫ β).c.app U = β.c.app U ≫ α.c.app (op ((Opens.map β.base).obj (unop U))) :=
  rfl

theorem congr_app {X Y : PresheafedSpace C} {α β : X ⟶ Y} (h : α = β) (U) :
    α.c.app U = β.c.app U ≫ X.presheaf.map (eqToHom (by subst h; rfl)) := by
  subst h
  simp

section

variable (C)

@[simps]
def forget : PresheafedSpace C ⥤ TopCat where
  obj X := (X : TopCat)
  map f := f.base

end

section Iso

variable {X Y : PresheafedSpace C}

@[simps hom inv]
def isoOfComponents (H : X.1 ≅ Y.1) (α : H.hom _* X.2 ≅ Y.2) : X ≅ Y where
  hom :=
    { base := H.hom
      c := α.inv }
  inv :=
    { base := H.inv
      c := Presheaf.toPushforwardOfIso H α.hom }
  hom_inv_id := by ext <;> simp
  inv_hom_id := by
    ext
    · dsimp
      rw [H.inv_hom_id]
    dsimp
    simp only [Presheaf.toPushforwardOfIso_app, assoc, ← α.hom.naturality]
    simp only [eqToHom_map, eqToHom_app, eqToHom_trans_assoc, eqToHom_refl, id_comp]
    apply Iso.inv_hom_id_app

@[simps]
def sheafIsoOfIso (H : X ≅ Y) : Y.2 ≅ H.hom.base _* X.2 where
  hom := H.hom.c
  inv := Presheaf.pushforwardToOfIso ((forget _).mapIso H).symm H.inv.c
  hom_inv_id := by
    ext U
    rw [NatTrans.comp_app]
    simpa using congr_arg (fun f => f ≫ eqToHom _) (congr_app H.inv_hom_id (op U))
  inv_hom_id := by
    ext U
    dsimp
    rw [NatTrans.id_app]
    simp only [Presheaf.pushforwardToOfIso_app, Iso.symm_inv, mapIso_hom, forget_map,
      Iso.symm_hom, mapIso_inv, eqToHom_map, assoc]
    have eq₁ := congr_app H.hom_inv_id (op ((Opens.map H.hom.base).obj U))
    have eq₂ := H.hom.c.naturality (eqToHom (congr_obj (congr_arg Opens.map
      ((forget C).congr_map H.inv_hom_id.symm)) U)).op
    rw [id_c, NatTrans.id_app, id_comp, eqToHom_map, comp_c_app] at eq₁
    rw [eqToHom_op, eqToHom_map] at eq₂
    erw [eq₂, reassoc_of% eq₁]
    simp

instance base_isIso_of_iso (f : X ⟶ Y) [IsIso f] : IsIso f.base :=
  ((forget _).mapIso (asIso f)).isIso_hom

instance c_isIso_of_iso (f : X ⟶ Y) [IsIso f] : IsIso f.c :=
  (sheafIsoOfIso (asIso f)).isIso_hom

theorem isIso_of_components (f : X ⟶ Y) [IsIso f.base] [IsIso f.c] : IsIso f :=
  (isoOfComponents (asIso f.base) (asIso f.c).symm).isIso_hom

end Iso

section Restrict

@[simps]
def restrict {U : TopCat} (X : PresheafedSpace C) {f : U ⟶ (X : TopCat)}
    (h : IsOpenEmbedding f) : PresheafedSpace C where
  carrier := U
  presheaf := h.isOpenMap.functor.op ⋙ X.presheaf

@[simps]
def ofRestrict {U : TopCat} (X : PresheafedSpace C) {f : U ⟶ (X : TopCat)}
    (h : IsOpenEmbedding f) : X.restrict h ⟶ X where
  base := f
  c :=
    { app := fun V => X.presheaf.map (h.isOpenMap.adjunction.counit.app V.unop).op
      naturality := fun U V f =>
        show _ = _ ≫ X.presheaf.map _ by
          rw [← map_comp, ← map_comp]
          rfl }

instance ofRestrict_mono {U : TopCat} (X : PresheafedSpace C) (f : U ⟶ X.1)
    (hf : IsOpenEmbedding f) : Mono (X.ofRestrict hf) := by
  haveI : Mono f := (TopCat.mono_iff_injective _).mpr hf.injective
  constructor
  intro Z g₁ g₂ eq
  ext1
  · have := congr_arg PresheafedSpace.Hom.base eq
    simp only [PresheafedSpace.comp_base, PresheafedSpace.ofRestrict_base] at this
    rw [cancel_mono] at this
    exact this
  · ext V
    have hV : (Opens.map (X.ofRestrict hf).base).obj (hf.isOpenMap.functor.obj V) = V := by
      ext1
      exact Set.preimage_image_eq _ hf.injective
    haveI :
      IsIso (hf.isOpenMap.adjunction.counit.app (unop (op (hf.isOpenMap.functor.obj V)))) :=
        NatIso.isIso_app_of_isIso
          (whiskerLeft hf.isOpenMap.functor hf.isOpenMap.adjunction.counit) V
    have := PresheafedSpace.congr_app eq (op (hf.isOpenMap.functor.obj V))
    rw [PresheafedSpace.comp_c_app, PresheafedSpace.comp_c_app,
      PresheafedSpace.ofRestrict_c_app, Category.assoc, cancel_epi] at this
    have h : _ ≫ _ = _ ≫ _ ≫ _ :=
      congr_arg (fun f => (X.restrict hf).presheaf.map (eqToHom hV).op ≫ f) this
    simp only [g₁.c.naturality, g₂.c.naturality_assoc] at h
    simp only [eqToHom_op, eqToHom_unop, eqToHom_map, eqToHom_trans,
      ← IsIso.comp_inv_eq, inv_eqToHom, Category.assoc] at h
    simpa using h

theorem restrict_top_presheaf (X : PresheafedSpace C) :
    (X.restrict (Opens.isOpenEmbedding ⊤)).presheaf =
      (Opens.inclusionTopIso X.carrier).inv _* X.presheaf := by
  dsimp
  rw [Opens.inclusion'_top_functor X.carrier]
  rfl

theorem ofRestrict_top_c (X : PresheafedSpace C) :
    (X.ofRestrict (Opens.isOpenEmbedding ⊤)).c =
      eqToHom
        (by
          rw [restrict_top_presheaf, ← Presheaf.Pushforward.comp_eq]
          erw [Iso.inv_hom_id]
          rw [Presheaf.id_pushforward]
          dsimp) := by
  /- another approach would be to prove the left hand side
       is a natural isomorphism, but I encountered a universe
       issue when `apply NatIso.isIso_of_isIso_app`. -/
  ext
  dsimp [ofRestrict]
  erw [eqToHom_map, eqToHom_app]
  simp

@[simps]
def toRestrictTop (X : PresheafedSpace C) : X ⟶ X.restrict (Opens.isOpenEmbedding ⊤) where
  base := (Opens.inclusionTopIso X.carrier).inv
  c := eqToHom (restrict_top_presheaf X)

@[simps]
def restrictTopIso (X : PresheafedSpace C) : X.restrict (Opens.isOpenEmbedding ⊤) ≅ X where
  hom := X.ofRestrict _
  inv := X.toRestrictTop
  hom_inv_id := by
    ext
    · rfl
    · erw [comp_c, toRestrictTop_c, whiskerRight_id',
        comp_id, ofRestrict_top_c, eqToHom_map, eqToHom_trans, eqToHom_refl]
      rfl
  inv_hom_id := by
    ext
    · rfl
    · erw [comp_c, ofRestrict_top_c, toRestrictTop_c, eqToHom_map, whiskerRight_id', comp_id,
        eqToHom_trans, eqToHom_refl]
      rfl

end Restrict

@[simps]
def Γ : (PresheafedSpace C)ᵒᵖ ⥤ C where
  obj X := (unop X).presheaf.obj (op ⊤)
  map f := f.unop.c.app (op ⊤)

theorem Γ_obj_op (X : PresheafedSpace C) : Γ.obj (op X) = X.presheaf.obj (op ⊤) :=
  rfl

theorem Γ_map_op {X Y : PresheafedSpace C} (f : X ⟶ Y) : Γ.map f.op = f.c.app (op ⊤) :=
  rfl

end PresheafedSpace

end AlgebraicGeometry

open AlgebraicGeometry AlgebraicGeometry.PresheafedSpace

variable {C}

namespace CategoryTheory

variable {D : Type*} [Category D]

namespace Functor

def mapPresheaf (F : C ⥤ D) : PresheafedSpace C ⥤ PresheafedSpace D where
  obj X :=
    { carrier := X.carrier
      presheaf := X.presheaf ⋙ F }
  map f :=
    { base := f.base
      c := whiskerRight f.c F }
  -- Porting note: these proofs were automatic in mathlib3
  map_id X := by
    ext U
    · rfl
    · simp
  map_comp f g := by
    ext U
    · rfl
    · simp

@[simp]
theorem mapPresheaf_obj_X (F : C ⥤ D) (X : PresheafedSpace C) :
    (F.mapPresheaf.obj X : TopCat) = (X : TopCat) :=
  rfl

@[simp]
theorem mapPresheaf_obj_presheaf (F : C ⥤ D) (X : PresheafedSpace C) :
    (F.mapPresheaf.obj X).presheaf = X.presheaf ⋙ F :=
  rfl

@[simp]
theorem mapPresheaf_map_f (F : C ⥤ D) {X Y : PresheafedSpace C} (f : X ⟶ Y) :
    (F.mapPresheaf.map f).base = f.base :=
  rfl

@[simp]
theorem mapPresheaf_map_c (F : C ⥤ D) {X Y : PresheafedSpace C} (f : X ⟶ Y) :
    (F.mapPresheaf.map f).c = whiskerRight f.c F :=
  rfl

end Functor

namespace NatTrans

def onPresheaf {F G : C ⥤ D} (α : F ⟶ G) : G.mapPresheaf ⟶ F.mapPresheaf where
  app X :=
    { base := 𝟙 _
      c := whiskerLeft X.presheaf α ≫ eqToHom (Presheaf.Pushforward.id_eq _).symm }

end NatTrans

end CategoryTheory
